import { IInputs } from "../generated/ManifestTypes";
import { canComplete, canEdit, dateRule, eventDate, mapPriority, mapState, previewColumns, quickEdit, ruledTypes, withStatusDetails } from "../model/activityTypes";
import { allowsAllTypes, DateRule, FeedSort, ROLLUP_TABLES, RollupType, SortColumn, SortOrder, TimelineConfig } from "../model/config";
import { DateEnv, formatFull } from "../model/dates";
import { applyChanges } from "../model/edit";
import { compareByDate, isOpenState } from "../model/feed";
import { looksLikeHtml, makeSnippet, noteHeading, threadKeyFor } from "../model/html";
import {
    ActivityTypeInfo, AttachmentRef, Counts, EditValues, ItemChanges, ItemDetails, ItemState, PartyRef, StatusOption, PreviewField, RecordContext,
    StateLabels, TimelineFilters, TimelineItem,
} from "../model/types";
import { FeedPagers, FileContent, HydratingPager, MergedPager, NewNote, SearchHits, SearchPager, Stream, StreamPage, TimelineDataSource } from "./dataSource";

type Row = Record<string, unknown>;

const FORMATTED = "@OData.Community.Display.V1.FormattedValue";
const LOOKUP_TYPE = "@Microsoft.Dynamics.CRM.lookuplogicalname";
/** Item ids per details query; keeps the URL well within limits */
const DETAILS_CHUNK = 25;
/** The real form opens at the width of the preview it replaces */
const PREVIEW_WIDTH = 560;

/** What the feed queries load: enough to place, sort and label an item. Bodies and participants follow for shown items only. */
const FEED_COLUMNS = [
    "activityid", "activitytypecode", "subject", "statecode", "statuscode", "prioritycode",
    "scheduledstart", "scheduledend", "actualend", "actualdurationminutes", "createdon", "modifiedon", "sortdate",
    "senton", "ownerid", "createdby",
];
/** The same columns for a Web API query of one activity */
const LIGHT_SELECT = FEED_COLUMNS.map((c) => (c === "ownerid" || c === "createdby" ? `_${c}_value` : c)).join(",");
/** Emails keep their attachment count, so it comes along with the feed; other types are counted when shown */
const EMAIL_ATTACHMENTS = "email_attachmentcount";
const PARTY_EXPAND = "activitypointer_activity_parties($select=participationtypemask,_partyid_value,addressused)";
const NOTE_SELECT = "annotationid,subject,notetext,filename,filesize,mimetype,isdocument,createdon,modifiedon,_createdby_value,_ownerid_value";
/** When sorting by activity date, an activity can sit at any of these */
const EVENT_DATE_COLUMNS: SortColumn[] = ["createdon", "scheduledstart", "scheduledend", "actualend"];
/** Records with more activities than fit on a page, kept for the browser session so they go straight to paging */
const LARGE_RECORDS = "rsn-activitytimeline:large";

// --- value helpers ----------------------------------------------------------------------------------------

function str(row: Row, key: string): string | undefined {
    const v = row[key];
    return typeof v === "string" && v.length > 0 ? v : undefined;
}

function num(row: Row, key: string): number | undefined {
    const v = row[key];
    return typeof v === "number" ? v : undefined;
}

function date(row: Row, key: string): Date | undefined {
    const v = row[key];
    if (typeof v !== "string" || v.length === 0) return undefined;
    const d = new Date(v);
    return isNaN(d.getTime()) ? undefined : d;
}

function formatted(row: Row, key: string): string | undefined {
    return str(row, `${key}${FORMATTED}`);
}

function lookup(row: Row, attribute: string): PartyRef | undefined {
    const id = str(row, `_${attribute}_value`);
    if (!id) return undefined;
    return { id, entity: str(row, `_${attribute}_value${LOOKUP_TYPE}`), name: formatted(row, `_${attribute}_value`) ?? "" };
}

function normalizeId(id: string): string {
    return id.replace(/[{}]/g, "").toLowerCase();
}

function odataString(value: string): string {
    return `'${value.replace(/'/g, "''")}'`;
}

/** A search term as an OData string: wildcard characters match literally, and it's encoded because options go into the URL as they are */
function searchLiteral(term: string): string {
    return encodeURIComponent(odataString(term.trim().replace(/[%_[]/g, "[$&]")));
}

/** A search term as a FetchXML like pattern: found anywhere, with wildcard characters matching literally */
function likePattern(term: string): string {
    return `%${term.trim().replace(/[%_[]/g, "[$&]")}%`;
}

function xmlValue(value: string): string {
    return value.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
}

// --- FetchXML -------------------------------------------------------------------------------------------
// Activity queries are FetchXML, so the same query runs on the record's own activities and through Dataverse's rollup.

/** A FetchXML filter part: a condition, a filter, or a link-entity inside a filter */
type Cond = string;

function condition(attribute: string, operator: string, value?: string | number): Cond {
    return value === undefined
        ? `<condition attribute="${attribute}" operator="${operator}" />`
        : `<condition attribute="${attribute}" operator="${operator}" value="${xmlValue(String(value))}" />`;
}

/** A condition no row meets, for a list of types none of which exist */
const NOTHING = condition("activityid", "null");

function valuesIn(attribute: string, values: (string | number)[], operator: "in" | "not-in" = "in"): Cond {
    return `<condition attribute="${attribute}" operator="${operator}">${values.map((v) => `<value>${xmlValue(String(v))}</value>`).join("")}</condition>`;
}

function group(type: "and" | "or", conditions: (Cond | undefined)[]): Cond | undefined {
    const list = conditions.filter((c): c is Cond => !!c);
    return list.length <= 1 ? list[0] : `<filter type="${type}">${list.join("")}</filter>`;
}

const anyOf = (conditions: (Cond | undefined)[]) => group("or", conditions);
const allOf = (conditions: (Cond | undefined)[]) => group("and", conditions);

const OPEN = valuesIn("statecode", [0, 3]);
const CLOSED = valuesIn("statecode", [1, 2]);

/** Type codes by logical name; a type with no code has no table, so nothing can be of it */
type TypeCodes = Map<string, number>;

function codesOf(types: string[], codes: TypeCodes): number[] {
    return types.flatMap((t) => {
        const code = codes.get(t);
        return code === undefined ? [] : [code];
    });
}

/** FetchXML compares activity types by object type code, not by name */
function typeIn(types: string[], codes: TypeCodes): Cond {
    const values = codesOf(types, codes);
    return values.length > 0 ? valuesIn("activitytypecode", values) : NOTHING;
}

function typeNotIn(types: string[], codes: TypeCodes): Cond | undefined {
    const values = codesOf(types, codes);
    return values.length > 0 ? valuesIn("activitytypecode", values, "not-in") : undefined;
}

/** Where a page of a FetchXML query starts */
interface PageCursor {
    page: number;
    cookie?: string;
}

/** One FetchXML query on activities, before the record's scope is added */
interface ActivityFetch {
    filter?: Cond;
    orders: [string, SortOrder][];
    count: number;
    page?: PageCursor;
    /** Whether rows can be emails, so their attachment count comes along */
    emails?: boolean;
    columns?: string[];
}

/** One page of a FetchXML query, in the Web API's row shape, and whether there's more */
interface FetchPage {
    rows: Row[];
    more: boolean;
    cookie?: string;
}

/**
 * Which activities a query covers. rollup: Dataverse's timeline rollup for the record (RetrieveTimelineWallRecords);
 * parties: regarding the record or with the record as a participant; regarding: regarding the record only.
 */
type Scope = "rollup" | "parties" | "regarding";

/** Every activity in scope as light rows, newest first; only for records with no more than a page of them */
interface Snapshot {
    rows: Row[];
    scope: Scope;
}

/** The feed's two sections built from a snapshot, in display order */
interface MemoryFeed {
    history: TimelineItem[];
    upcoming: TimelineItem[];
}

const ROLLUP_CODES: Record<RollupType, number> = { none: 0, related: 1, extended: 2 };

const WEB_API_HEADERS = {
    Accept: "application/json",
    "OData-MaxVersion": "4.0",
    "OData-Version": "4.0",
    Prefer: 'odata.include-annotations="*"',
};

/** One query of the feed: some activity types in some states, ordered by one date column. */
interface Slice {
    column: SortColumn;
    condition?: (codes: TypeCodes) => Cond | undefined;
    /** States the slice can hold, so a status filter can leave it out */
    states: "open" | "closed" | "any";
    /** Types it can hold, so it's skipped when the record has none; undefined = any type */
    types?: string[];
}

/** Activity counts per type and state, plus notes. Also tells the feed which queries can be skipped. */
interface TypeStates {
    rows: { entity: string; label: string; open: boolean; count: number }[];
    notes: number;
    /** What the counts covered; they can only rule out queries in the same scope */
    scope: Scope;
    /** False when some counted type couldn't be named; then nothing is ruled out */
    complete: boolean;
}

/**
 * FetchXML returns activity types as object type codes. These are fixed for system tables;
 * custom activity tables get theirs from metadata.
 */
const SYSTEM_TYPE_CODES: Record<number, string> = {
    4201: "appointment", 4202: "email", 4204: "fax", 4206: "incidentresolution", 4207: "letter", 4208: "opportunityclose",
    4209: "orderclose", 4210: "phonecall", 4211: "quoteclose", 4212: "task", 4214: "serviceappointment", 4216: "socialactivity",
    4251: "recurringappointmentmaster", 4401: "campaignresponse", 4402: "campaignactivity", 4406: "bulkoperation",
};
const SYSTEM_CODES_BY_NAME: TypeCodes = new Map(Object.entries(SYSTEM_TYPE_CODES).map(([code, name]) => [name, Number(code)]));
const EMAIL_CODE = 4202;

// --- rollup results -------------------------------------------------------------------------------------

/** An entity as RetrieveTimelineWallRecords returns it: the SDK's shape, serialized */
interface SdkEntity {
    Attributes?: { Key: string; Value: unknown }[];
    FormattedValues?: { Key: string; Value: string }[];
}

interface SdkReference {
    Id: string;
    LogicalName: string;
    Name?: string | null;
}

function isReference(value: unknown): value is SdkReference {
    return !!value && typeof value === "object" && "Id" in value && "LogicalName" in value;
}

/** Aliased values (link-entity columns, aggregates) and option set values are wrapped in { Value } */
function unwrap(value: unknown): unknown {
    let v = value;
    while (v && typeof v === "object" && !Array.isArray(v) && "Value" in v && !isReference(v)) v = (v as { Value: unknown }).Value;
    return v;
}

/** Puts a rolled-up row in the Web API's shape, so one mapping serves both kinds of query */
function webApiRow(entity: SdkEntity): Row {
    const row: Row = {};
    const lookups = new Set<string>();
    for (const { Key, Value } of entity.Attributes ?? []) {
        const value = unwrap(Value);
        if (isReference(value)) {
            row[`_${Key}_value`] = value.Id;
            row[`_${Key}_value${LOOKUP_TYPE}`] = value.LogicalName;
            if (value.Name) row[`_${Key}_value${FORMATTED}`] = value.Name;
            lookups.add(Key);
        } else {
            row[Key] = value;
        }
    }
    for (const { Key, Value } of entity.FormattedValues ?? []) {
        row[`${lookups.has(Key) ? `_${Key}_value` : Key}${FORMATTED}`] = Value;
    }
    return row;
}

/** The Web API returns the paging cookie wrapped and URL-encoded twice; FetchXML wants the cookie itself */
function pagingCookie(annotation: unknown): string | undefined {
    if (typeof annotation !== "string") return undefined;
    const encoded = /pagingcookie="([^"]*)"/.exec(annotation)?.[1];
    return encoded ? decodeURIComponent(decodeURIComponent(encoded)) : undefined;
}

const INTERNAL_PARTY_TYPES = new Set(["systemuser", "queue", "team"]);

interface MetadataAttribute {
    DisplayName?: string;
    /** Choice labels by value, in the user's language (model-driven apps) */
    OptionSet?: Record<string, { text?: string } | undefined>;
    AttributeType?: number | string;
    AttributeTypeName?: { value?: string };
    /** Status reasons with their states. Not in the public typings; without it the status can't be changed from here. */
    attributeDescriptor?: { OptionSet?: { Label?: string; Value?: number; State?: number; IsHidden?: boolean }[] };
}

interface MetadataLike {
    DisplayName?: string;
    EntitySetName?: string;
    Attributes?: { get?: (name: string) => MetadataAttribute | undefined };
}

/** Lookup-like attribute types: Customer = 1, Lookup = 6, Owner = 9 */
function isLookupAttribute(attr: MetadataAttribute | undefined): boolean {
    if (!attr) return false;
    const t = attr.AttributeType;
    if (t === 1 || t === 6 || t === 9 || t === "Lookup" || t === "Customer" || t === "Owner") return true;
    const name = attr.AttributeTypeName?.value;
    return name === "LookupType" || name === "CustomerType" || name === "OwnerType";
}

interface XrmWindow {
    Xrm?: { Navigation?: { navigateTo?: (page: Record<string, unknown>, options: Record<string, unknown>) => Promise<unknown> } };
}

export class DataverseDataSource implements TimelineDataSource {
    public readonly currentUserId: string;
    private readonly metadataCache = new Map<string, Promise<MetadataLike | undefined>>();
    /** Narrowed for the rest of the session when Dataverse refuses a scope, so the timeline still loads */
    private scope: Scope;

    constructor(
        private readonly context: ComponentFramework.Context<IInputs>,
        private readonly record: RecordContext,
        private readonly config: TimelineConfig,
        private readonly env: DateEnv,
        private readonly labels: { note: string; untitled: string },
    ) {
        this.currentUserId = normalizeId(context.userSettings.userId ?? "");
        this.scope = config.rollup !== "none" && ROLLUP_TABLES.includes(record.entity) ? "rollup" : this.ownScope();
    }

    // --- queries ------------------------------------------------------------------------------------------

    /** The record's own activities, as the form is configured */
    private ownScope(): Scope {
        return this.config.includeParties ? "parties" : "regarding";
    }

    /** The scope to retry with when Dataverse refuses one */
    private narrower(scope: Scope): Scope | undefined {
        if (scope === "rollup") return this.ownScope();
        return scope === "parties" ? "regarding" : undefined;
    }

    /**
     * The scope as a filter part; with rollup Dataverse adds it. Dataverse keeps an activity's regarding record among its
     * parties too (participation type Regarding), so one indexed condition on parties covers both, as in the built-in
     * timeline. "any" checks parties without multiplying rows.
     */
    private scopeCondition(scope: Scope): Cond | undefined {
        if (scope === "rollup") return undefined;
        const id = normalizeId(this.record.id);
        if (scope === "regarding") return condition("regardingobjectid", "eq", id);
        return `<link-entity name="activityparty" from="activityid" to="activityid" link-type="any"><filter>${condition("partyid", "eq", id)}</filter></link-entity>`;
    }

    /**
     * Runs an activity query in the current scope. When Dataverse refuses the scope (rollup on a table it can't roll
     * up, or the participant filter), the rest of the session uses the next narrower one, and the query runs again.
     */
    private async queryActivities(build: (scope: Cond | undefined, rollup: boolean) => string): Promise<FetchPage & { scope: Scope }> {
        const scope = this.scope;
        try {
            const rollup = scope === "rollup";
            return { ...(await this.runFetch(build(this.scopeCondition(scope), rollup), rollup)), scope };
        } catch (e) {
            const narrower = this.narrower(scope);
            if (!narrower || !(e as { rejected?: boolean }).rejected) throw e;
            // Queries run side by side; one of the others may have narrowed it already
            if (this.scope === scope) this.scope = narrower;
            return this.queryActivities(build);
        }
    }

    /** Runs FetchXML on activities: as a Web API query, or through the rollup the built-in timeline uses */
    private async runFetch(fetchXml: string, rollup: boolean): Promise<FetchPage> {
        const url = rollup
            ? "/api/data/v9.2/activitypointers/Microsoft.Dynamics.CRM.RetrieveTimelineWallRecords(FetchXml=@xml,Target=@target,RollupType=@type)" +
              `?@xml=${encodeURIComponent(odataString(fetchXml))}&@target=${encodeURIComponent(await this.rollupTarget())}&@type=${ROLLUP_CODES[this.config.rollup]}`
            : `/api/data/v9.2/activitypointers?fetchXml=${encodeURIComponent(fetchXml)}`;
        // context.webAPI can't call functions, so both go through fetch, the same way
        const response = await fetch(url, { headers: WEB_API_HEADERS, credentials: "same-origin" });
        const body = (await response.json().catch(() => ({}))) as Row;
        if (!response.ok) {
            const message = (body.error as { message?: string } | undefined)?.message ?? `Dataverse answered ${response.status}.`;
            // 400: Dataverse refused the query itself, so a narrower scope can still work
            throw Object.assign(new Error(message), { rejected: response.status === 400 });
        }
        if (rollup) {
            const collection = JSON.parse(typeof body.TimelineWallRecords === "string" ? body.TimelineWallRecords : "{}") as {
                Entities?: SdkEntity[];
                MoreRecords?: boolean;
                PagingCookie?: string | null;
            };
            return { rows: (collection.Entities ?? []).map(webApiRow), more: collection.MoreRecords === true, cookie: collection.PagingCookie ?? undefined };
        }
        return {
            rows: (body.value as Row[] | undefined) ?? [],
            more: body["@Microsoft.Dynamics.CRM.morerecords"] === true,
            cookie: pagingCookie(body["@Microsoft.Dynamics.CRM.fetchxmlpagingcookie"]),
        };
    }

    /** The record, as the rollup's Target parameter */
    private async rollupTarget(): Promise<string> {
        const entitySet = (await this.metadata(this.record.entity, []))?.EntitySetName;
        if (!entitySet) throw Object.assign(new Error(`Couldn't find the entity set for ${this.record.entity}.`), { rejected: true });
        return `{'@odata.id':'${entitySet}(${normalizeId(this.record.id)})'}`;
    }

    /** One FetchXML query on activities, with the scope added */
    private activityFetch(q: ActivityFetch, scope: Cond | undefined, rollup: boolean): string {
        const paging = q.page ? ` page="${q.page.page}"${q.page.cookie ? ` paging-cookie="${xmlValue(q.page.cookie)}"` : ""}` : "";
        // An activity can be related to the record more than one way; the built-in timeline asks for it once, too
        const distinct = rollup ? ` distinct="true"` : "";
        const columns = (q.columns ?? FEED_COLUMNS).map((c) => `<attribute name="${c}" />`).join("");
        const orders = q.orders.map(([c, o]) => `<order attribute="${c}" descending="${o === "desc"}" />`).join("");
        const emails = q.emails
            ? `<link-entity name="email" from="activityid" to="activityid" link-type="outer" alias="email"><attribute name="attachmentcount" alias="${EMAIL_ATTACHMENTS}" /></link-entity>`
            : "";
        const filter = allOf([scope, q.filter]);
        return `<fetch count="${q.count}"${paging}${distinct}><entity name="activitypointer">${columns}${orders}${emails}` +
            `${filter ? `<filter type="and">${filter}</filter>` : ""}</entity></fetch>`;
    }

    private readonly codeCache = new Map<string, Promise<number | undefined>>();

    /** Type codes for activity types by name: fixed for system tables, from cached metadata for custom ones */
    private async codesFor(types: Iterable<string>): Promise<TypeCodes> {
        const names = Array.from(new Set(types));
        const codes = await Promise.all(
            names.map((name) => {
                const known = SYSTEM_CODES_BY_NAME.get(name);
                if (known !== undefined) return Promise.resolve(known);
                let code = this.codeCache.get(name);
                if (!code) {
                    code = this.metadata(name, []).then((md) => (md as { ObjectTypeCode?: number } | undefined)?.ObjectTypeCode);
                    this.codeCache.set(name, code);
                }
                return code;
            }),
        );
        const map: TypeCodes = new Map();
        names.forEach((name, i) => {
            const code = codes[i];
            if (typeof code === "number") map.set(name, code);
        });
        return map;
    }

    /** Activity types to query: configured types, narrowed by the user's type filter. Undefined = all types. */
    private activityTypes(filters?: TimelineFilters): string[] | undefined {
        const configured = allowsAllTypes(this.config) ? undefined : this.config.activityTypes;
        const chosen = filters?.types.filter((t) => t !== "annotation") ?? [];
        if (filters && filters.types.length > 0) {
            return configured ? chosen.filter((t) => configured.includes(t)) : chosen;
        }
        return configured;
    }

    /** The date filter's window, or undefined for any date */
    private dateWindow(filters: TimelineFilters): { from: string; to: string } | undefined {
        const f = filters.date;
        if (f.kind !== "last") return undefined;
        const now = this.env.now();
        return { from: new Date(now.getTime() - f.days * 86400000).toISOString(), to: now.toISOString() };
    }

    /** The date filter for notes, in OData */
    private dateFilter(filters: TimelineFilters, column: string): string[] {
        const w = this.dateWindow(filters);
        return w ? [`${column} ge ${w.from}`, `${column} le ${w.to}`] : [];
    }

    /** The date filter for activities, in FetchXML */
    private dateConditions(filters: TimelineFilters, column: string): Cond[] {
        const w = this.dateWindow(filters);
        return w ? [condition(column, "ge", w.from), condition(column, "le", w.to)] : [];
    }

    private ownerCondition(filters: TimelineFilters): Cond | undefined {
        return filters.onlyMine && this.currentUserId ? condition("ownerid", "eq", this.currentUserId) : undefined;
    }

    private notesWanted(filters?: TimelineFilters): boolean {
        if (!this.config.includeNotes) return false;
        if (!filters) return true;
        if (filters.status !== "all") return false;
        return filters.types.length === 0 || filters.types.includes("annotation");
    }

    private statusCondition(filters: TimelineFilters): Cond | undefined {
        switch (filters.status) {
            case "open": return OPEN;
            case "completed": return condition("statecode", "eq", 1);
            case "overdue": return allOf([OPEN, condition("scheduledend", "lt", this.env.now().toISOString()), condition("activitytypecode", "ne", EMAIL_CODE)]);
            default: return undefined;
        }
    }

    // --- counts -------------------------------------------------------------------------------------------

    /** Counts the activities in scope, grouped as asked. Rolled up, an activity related more than one way counts once. */
    private async aggregate(groupBy: string, filter?: Cond): Promise<{ rows: Row[]; scope: Scope }> {
        const result = await this.queryActivities((scope, rollup) => {
            const where = allOf([scope, filter]);
            const count = rollup
                ? `<attribute name="activityid" alias="n" aggregate="countcolumn" distinct="true" />`
                : `<attribute name="activityid" alias="n" aggregate="count" />`;
            return `<fetch aggregate="true"><entity name="activitypointer">${count}${groupBy}${where ? `<filter type="and">${where}</filter>` : ""}</entity></fetch>`;
        });
        return { rows: result.rows, scope: result.scope };
    }

    private typeCodesPromise?: Promise<Map<number, string>>;

    /** Object type code to logical name for every activity type the timeline can show */
    private typeCodes(): Promise<Map<number, string>> {
        this.typeCodesPromise ??= this.loadTypeCodes();
        return this.typeCodesPromise;
    }

    private async loadTypeCodes(): Promise<Map<number, string>> {
        const map = new Map(Object.entries(SYSTEM_TYPE_CODES).map(([code, name]) => [Number(code), name]));
        const known = new Set(map.values());
        if (allowsAllTypes(this.config)) {
            // Any custom activity table can show up; one metadata request names them all
            try {
                const response = await fetch("/api/data/v9.2/EntityDefinitions?$select=LogicalName,ObjectTypeCode&$filter=IsActivity eq true", {
                    headers: { Accept: "application/json" },
                    credentials: "same-origin",
                });
                const body = response.ok ? ((await response.json()) as { value?: { LogicalName?: string; ObjectTypeCode?: number }[] }) : {};
                body.value?.forEach((e) => {
                    if (e.LogicalName && typeof e.ObjectTypeCode === "number") map.set(e.ObjectTypeCode, e.LogicalName);
                });
            } catch {
                // Unnamed types are left out of the counts
            }
        } else {
            await Promise.all(
                this.config.activityTypes
                    .filter((t) => !known.has(t))
                    .map(async (t) => {
                        const code = ((await this.metadata(t, [])) as { ObjectTypeCode?: number } | undefined)?.ObjectTypeCode;
                        if (typeof code === "number") map.set(code, t);
                    }),
            );
        }
        return map;
    }

    private snapshotPromise?: Promise<Snapshot | undefined>;

    /** The record's activities from one query, or undefined when it has more than fit; `fresh` loads them again */
    private snapshot(fresh: boolean): Promise<Snapshot | undefined> {
        if (fresh || !this.snapshotPromise) {
            if (fresh) this.forgetDetails();
            // Without a snapshot, counts and feed query the way they do for large records
            this.snapshotPromise = this.loadSnapshot().catch(() => undefined);
        }
        return this.snapshotPromise;
    }

    /**
     * A record with no more activities than fit on a page gets them all in this one query, and its counts, feed and
     * filters work from that. A larger record pages through one query per date column instead.
     */
    private async loadSnapshot(): Promise<Snapshot | undefined> {
        const key = `${LARGE_RECORDS}:${this.record.entity}:${normalizeId(this.record.id)}`;
        if (readSessionFlag(key)) return undefined;
        const types = this.activityTypes();
        const codes = await this.codesFor(types ?? []);
        const result = await this.queryActivities((scope, rollup) => this.activityFetch({
            filter: types ? typeIn(types, codes) : undefined,
            orders: [["createdon", "desc"], ["activityid", "desc"]],
            count: this.config.pageSize,
            emails: !types || types.includes("email"),
        }, scope, rollup));
        if (result.more) {
            writeSessionFlag(key);
            return undefined;
        }
        return { rows: result.rows, scope: result.scope };
    }

    /** The record's own notes; notes don't roll up */
    private countNotes(): Promise<number> {
        if (!this.config.includeNotes) return Promise.resolve(0);
        const xml = `<fetch aggregate="true"><entity name="annotation"><attribute name="annotationid" alias="n" aggregate="count" />` +
            `<filter><condition attribute="objectid" operator="eq" value="${xmlValue(normalizeId(this.record.id))}" /></filter></entity></fetch>`;
        return this.context.webAPI.retrieveMultipleRecords("annotation", `?fetchXml=${encodeURIComponent(xml)}`).then((r) => num((r.entities as Row[])[0] ?? {}, "n") ?? 0);
    }

    private async countTypeStates(snapshot: Promise<Snapshot | undefined>): Promise<TypeStates> {
        const notes = this.countNotes();
        // Handled when awaited below; this keeps a failure from being reported as unhandled while the snapshot loads
        notes.catch(() => undefined);
        const all = await snapshot;
        if (all) return { rows: countRows(all.rows), notes: await notes, scope: all.scope, complete: true };

        const allowed = this.activityTypes();
        const [codes, activities] = await Promise.all([
            this.typeCodes(),
            // Grouped by type and state; the types the timeline shows are picked out below
            this.aggregate(`<attribute name="activitytypecode" alias="type" groupby="true" /><attribute name="statecode" alias="state" groupby="true" />`),
        ]);
        const rows: TypeStates["rows"] = [];
        // Complete when every type the timeline shows has a name; other unnamed types don't matter then
        const named = new Set(codes.values());
        let complete = allowed ? allowed.every((t) => named.has(t)) : true;
        for (const r of activities.rows) {
            const entity = codes.get(num(r, "type") ?? -1);
            if (!entity) {
                if (!allowed) complete = false;
                continue;
            }
            if (allowed && !allowed.includes(entity)) continue;
            const state = mapState(num(r, "state"));
            rows.push({ entity, label: formatted(r, "type") ?? entity, open: state === "open" || state === "scheduled", count: num(r, "n") ?? 0 });
        }
        return { rows, notes: await notes, scope: activities.scope, complete };
    }

    private typeStatesPromise?: Promise<TypeStates | undefined>;
    /** The counts once they're in. Undefined while counting, so the feed never waits for them. */
    private counted?: TypeStates;

    /** Counts per type and state; `fresh` counts again (and loads the snapshot again), otherwise the last result is reused */
    private typeStates(fresh: boolean): Promise<TypeStates | undefined> {
        if (fresh || !this.typeStatesPromise) {
            // Old counts could rule out a type that has just got its first item
            this.counted = undefined;
            const promise: Promise<TypeStates | undefined> = this.countTypeStates(this.snapshot(fresh))
                .then((states) => {
                    if (this.typeStatesPromise === promise) this.counted = states;
                    return states;
                })
                .catch(() => undefined);
            this.typeStatesPromise = promise;
        }
        return this.typeStatesPromise;
    }

    private async countOverdue(): Promise<number> {
        const allowed = this.activityTypes();
        const [codes, result] = await Promise.all([
            this.typeCodes(),
            this.aggregate(`<attribute name="activitytypecode" alias="type" groupby="true" />`, allOf([OPEN, condition("scheduledend", "lt", this.env.now().toISOString())])),
        ]);
        return result.rows.reduce((sum, r) => {
            const entity = codes.get(num(r, "type") ?? -1);
            // Emails have no due date in the timeline's sense
            const counts = entity ? entity !== "email" && (!allowed || allowed.includes(entity)) : !allowed;
            return counts ? sum + (num(r, "n") ?? 0) : sum;
        }, 0);
    }

    public async getCounts(): Promise<Counts> {
        const counting = this.typeStates(true);
        // The snapshot the counts just asked for; without one, overdue items take an aggregate query of their own
        const snapshot = await this.snapshot(false);
        const [states, overdue] = await Promise.all([
            counting,
            snapshot ? Promise.resolve(countOverdueRows(snapshot.rows, this.env.now())) : this.countOverdue().catch(() => 0),
        ]);
        if (!states) throw new Error("Couldn't count the timeline's items.");

        const byType = new Map<string, { entity: string; label: string; count: number }>();
        let total = 0;
        let open = 0;
        for (const r of states.rows) {
            const entry = byType.get(r.entity) ?? { entity: r.entity, label: r.label, count: 0 };
            entry.count += r.count;
            byType.set(r.entity, entry);
            total += r.count;
            if (r.open) open += r.count;
        }
        if (states.notes > 0) byType.set("annotation", { entity: "annotation", label: this.labels.note, count: states.notes });
        return { total: total + states.notes, byType: Array.from(byType.values()), open, overdue };
    }

    /** False only when counts show the record has nothing the slice could return */
    private hasRows(states: TypeStates | undefined, slice: Pick<Slice, "states" | "types">): boolean {
        if (!states || !states.complete || states.scope !== this.scope) return true;
        return states.rows.some(
            (r) => r.count > 0 && (!slice.types || slice.types.includes(r.entity)) && (slice.states === "any" || (slice.states === "open") === r.open),
        );
    }

    // --- feed ---------------------------------------------------------------------------------------------

    /**
     * Splits the activities into one query per date column, so each can be paged by count and merged in date order.
     * Sorted by activity date, newest first, open items still ahead go to an upcoming section of their own.
     */
    private feedSlices(types: string[] | undefined, sort: FeedSort, withUpcoming: boolean): { history: Slice[]; upcoming: Slice[] } {
        if (sort.activities !== "eventdate") {
            return { history: [{ column: sort.activities, condition: types ? (c) => typeIn(types, c) : undefined, states: "any", types }], upcoming: [] };
        }
        const groups: Record<DateRule, string[]> = { created: [], start: [], due: [], completed: [] };
        const ruled = ruledTypes(this.config);
        if (types) types.forEach((t) => groups[dateRule(t, this.config)].push(t));
        else ruled.forEach((rule, entity) => groups[rule].push(entity));
        const { start, due, completed } = groups;
        const now = this.env.now().toISOString();
        const isNull = (column: string) => condition(column, "null");
        const notNull = (column: string) => condition(column, "not-null");

        // Placed by created on: types without a rule, plus ruled items that lack their date
        const created = (c: TypeCodes) => anyOf([
            types
                ? groups.created.length > 0 ? typeIn(groups.created, c) : undefined
                : ruled.size > 0 ? typeNotIn(Array.from(ruled.keys()), c) : undefined,
            start.length > 0 ? allOf([typeIn(start, c), isNull("scheduledstart")]) : undefined,
            due.length > 0 ? allOf([typeIn(due, c), anyOf([allOf([OPEN, isNull("scheduledend")]), allOf([CLOSED, isNull("actualend")])])]) : undefined,
            completed.length > 0 ? allOf([typeIn(completed, c), anyOf([OPEN, isNull("actualend")])]) : undefined,
        ]);
        const history: Slice[] = [];
        if (!types || groups.created.length + start.length + due.length + completed.length > 0) {
            // With all types allowed and no rules at all, the created slice is simply every activity
            history.push({ column: "createdon", condition: created, states: "any", types });
        }
        if (start.length > 0) {
            history.push({
                column: "scheduledstart",
                condition: (c) => allOf([typeIn(start, c), notNull("scheduledstart"), withUpcoming ? anyOf([CLOSED, condition("scheduledstart", "le", now)]) : undefined]),
                states: "any",
                types: start,
            });
        }
        if (due.length > 0) {
            history.push({
                column: "scheduledend",
                condition: (c) => allOf([typeIn(due, c), OPEN, notNull("scheduledend"), withUpcoming ? condition("scheduledend", "le", now) : undefined]),
                states: "open",
                types: due,
            });
        }
        const closable = [...due, ...completed];
        if (closable.length > 0) {
            history.push({ column: "actualend", condition: (c) => allOf([typeIn(closable, c), CLOSED, notNull("actualend")]), states: "closed", types: closable });
        }

        const upcoming: Slice[] = [];
        if (withUpcoming && start.length > 0) {
            upcoming.push({ column: "scheduledstart", condition: (c) => allOf([typeIn(start, c), OPEN, condition("scheduledstart", "gt", now)]), states: "open", types: start });
        }
        if (withUpcoming && due.length > 0) {
            upcoming.push({ column: "scheduledend", condition: (c) => allOf([typeIn(due, c), OPEN, condition("scheduledend", "gt", now)]), states: "open", types: due });
        }
        return { history, upcoming };
    }

    private sliceAllowed(slice: Slice, filters: TimelineFilters): boolean {
        if (filters.status === "all") return true;
        if (filters.status === "completed") return slice.states !== "open";
        return slice.states !== "closed";
    }

    public openFeed(filters: TimelineFilters, sort: FeedSort): FeedPagers {
        const hydrate = (items: TimelineItem[]) => this.hydrate(items);
        if (filters.search.trim()) {
            return { history: new HydratingPager(new SearchPager(() => this.search(filters, sort)), hydrate) };
        }

        const types = this.activityTypes(filters);
        const withUpcoming = sort.activities === "eventdate" && sort.order === "desc";
        const slices = types && types.length === 0 ? { history: [], upcoming: [] } : this.feedSlices(types, sort, withUpcoming);
        // Every type a slice can name; system types need nothing, custom ones come from cached metadata
        const codes = this.codesFor([...(types ?? []), ...ruledTypes(this.config).keys()]);
        // With every activity at hand, a section's first slice serves them all from memory and the others stay empty
        const memory = this.memoryFeed(filters, sort, withUpcoming);
        const stream = (slice: Slice, order: SortOrder, section: keyof MemoryFeed, first: boolean): Stream => ({
            fetch: async (cursor) => {
                const held = await memory;
                if (held) return first ? pageOf(held[section], cursor, this.config.pageSize) : { items: [] };
                return this.fetchSlice(filters, slice, sort, order, codes, cursor);
            },
        });

        const history = slices.history.filter((s) => this.sliceAllowed(s, filters)).map((s, i) => stream(s, sort.order, "history", i === 0));
        if (this.notesWanted(filters)) {
            // Notes are placed by created on when sorting by activity date
            const column = sort.activities === "eventdate" ? "createdon" : sort.notes;
            history.push({ fetch: (cursor) => this.fetchNotes(filters, column, sort.order, cursor) });
        }
        const pagers: FeedPagers = { history: new HydratingPager(new MergedPager(history, sort.order), hydrate) };

        const upcoming = filters.status === "overdue"
            ? []
            : slices.upcoming.filter((s) => this.sliceAllowed(s, filters)).map((s, i) => stream(s, "asc", "upcoming", i === 0));
        if (upcoming.length > 0) pagers.upcoming = new HydratingPager(new MergedPager(upcoming, "asc"), hydrate);
        return pagers;
    }

    /**
     * The feed from the snapshot, filtered, placed and split the way the slice queries do it.
     * Undefined without a snapshot, and then the slices query.
     */
    private async memoryFeed(filters: TimelineFilters, sort: FeedSort, withUpcoming: boolean): Promise<MemoryFeed | undefined> {
        const snapshot = await this.snapshot(false);
        if (!snapshot) return undefined;
        const types = this.activityTypes(filters);
        const now = this.env.now();
        const feed: MemoryFeed = { history: [], upcoming: [] };
        for (const r of snapshot.rows) {
            const item = this.mapActivity(r, sort.activities);
            if (types && !types.includes(item.entity)) continue;
            if (!matchesStatus(item, filters.status)) continue;
            if (filters.onlyMine && this.currentUserId && normalizeId(item.owner?.id ?? "") !== this.currentUserId) continue;
            // The date filter applies to the date that places the item; sorted by one column, items without it drop out
            if (filters.date.kind !== "any" && (!this.inDateFilter(filters, item.date) || (sort.activities !== "eventdate" && item.dateField !== sort.activities))) continue;
            const rule = dateRule(item.entity, this.config);
            const ahead = withUpcoming && isOpenState(item.state) &&
                ((rule === "start" && !!item.scheduledStart && item.scheduledStart > now) || (rule === "due" && !!item.scheduledEnd && item.scheduledEnd > now));
            (ahead ? feed.upcoming : feed.history).push(item);
        }
        feed.history.sort(compareByDate(sort.order));
        feed.upcoming.sort(compareByDate("asc"));
        return feed;
    }

    private async fetchSlice(
        filters: TimelineFilters, slice: Slice, sort: FeedSort, order: SortOrder, codes: Promise<TypeCodes>, cursor: string | undefined,
    ): Promise<StreamPage> {
        // Uses counts only when they're already in: waiting for them would hold up the first page
        if (!cursor && !this.hasRows(this.counted, slice)) return { items: [] };
        const page = cursor ? (JSON.parse(cursor) as PageCursor) : { page: 1 };
        const filter = allOf([
            slice.condition?.(await codes),
            ...this.dateConditions(filters, slice.column),
            this.statusCondition(filters),
            this.ownerCondition(filters),
        ]);
        const result = await this.queryActivities((scope, rollup) => this.activityFetch({
            filter,
            // Like the built-in timeline: with a single sort column, activities without a value in it end up last
            orders: [[slice.column, order], ["activityid", order]],
            count: this.config.pageSize,
            page,
            emails: !slice.types || slice.types.includes("email"),
        }, scope, rollup));
        return {
            items: result.rows.map((r) => this.mapActivity(r, sort.activities)),
            next: result.more ? JSON.stringify({ page: page.page + 1, cookie: result.cookie } as PageCursor) : undefined,
        };
    }

    private notesQuery(filters: TimelineFilters, column: string, order: SortOrder, extra: string[] = []): string {
        const conditions = [`_objectid_value eq ${normalizeId(this.record.id)}`, ...this.dateFilter(filters, column), ...extra];
        if (filters.onlyMine && this.currentUserId) conditions.push(`_ownerid_value eq ${this.currentUserId}`);
        return `?$select=${NOTE_SELECT}&$filter=${conditions.join(" and ")}&$orderby=${column} ${order},annotationid ${order}`;
    }

    private async fetchNotes(filters: TimelineFilters, column: string, order: SortOrder, cursor: string | undefined): Promise<StreamPage> {
        let options = cursor;
        if (!options) {
            if (this.counted?.notes === 0) return { items: [] };
            options = this.notesQuery(filters, column, order);
        }
        const result = await this.context.webAPI.retrieveMultipleRecords("annotation", options, this.config.pageSize);
        return { items: (result.entities as Row[]).map((r) => this.mapNote(r, column)), next: nextOptions(result.nextLink) };
    }

    // --- search -------------------------------------------------------------------------------------------

    /**
     * Searches titles and content with one query over activities and one over notes, however the feed is sorted:
     * wildcards on body text are the most expensive conditions the control uses. Only the newest activities are
     * looked through (searchLimit), and notes from the same period.
     */
    private async search(filters: TimelineFilters, sort: FeedSort): Promise<SearchHits> {
        const limit = this.config.searchLimit;
        const types = this.activityTypes(filters);
        const event = sort.activities === "eventdate";
        const [states, codes] = await Promise.all([this.typeStates(false), this.codesFor(types ?? [])]);
        // Every condition but the search term, so the newest `limit` activities are the ones searched
        const base = allOf([
            types ? typeIn(types, codes) : undefined,
            filters.date.kind !== "any" ? anyOf((event ? EVENT_DATE_COLUMNS : [sort.activities]).map((c) => allOf(this.dateConditions(filters, c)))) : undefined,
            this.statusCondition(filters),
            this.ownerCondition(filters),
        ]);
        const newestFirst: [string, SortOrder][] = [["createdon", "desc"], ["activityid", "desc"]];

        const hasActivities = (!types || types.length > 0) && this.hasRows(states, { states: "any", types });
        const from = hasActivities ? await this.searchStart(base, newestFirst, limit, states) : undefined;

        const searchActivities = async () => {
            if (!hasActivities) return [];
            const like = likePattern(filters.search);
            const result = await this.queryActivities((scope, rollup) => this.activityFetch({
                filter: allOf([base, from ? condition("createdon", "ge", from.toISOString()) : undefined, anyOf([condition("subject", "like", like), condition("description", "like", like)])]),
                orders: newestFirst,
                count: limit,
                emails: !types || types.includes("email"),
            }, scope, rollup));
            return result.rows.map((r) => this.mapActivity(r, sort.activities));
        };
        const searchNotes = async () => {
            if (!this.notesWanted(filters) || states?.notes === 0) return [];
            const column = event ? "createdon" : sort.notes;
            const term = searchLiteral(filters.search);
            const contains = `(contains(subject,${term}) or contains(notetext,${term}) or contains(filename,${term}))`;
            const since = from ? [`createdon ge ${from.toISOString()}`] : [];
            const result = await this.context.webAPI.retrieveMultipleRecords("annotation", this.notesQuery(filters, column, "desc", [contains, ...since]), limit);
            return (result.entities as Row[]).map((r) => this.mapNote(r, column));
        };

        const [activities, notes] = await Promise.all([searchActivities(), searchNotes()]);
        // By activity date the query asked for any date in the window; keep the ones placed there
        const items = [...activities, ...notes].filter((i) => this.inDateFilter(filters, i.date)).sort(compareByDate(sort.order));
        return { items, limit: from ? { count: limit, from } : undefined };
    }

    /** Created-on date of the oldest activity a search reaches; undefined when they all fit within the limit */
    private async searchStart(base: Cond | undefined, orders: [string, SortOrder][], limit: number, states: TypeStates | undefined): Promise<Date | undefined> {
        if (states?.complete && states.scope === this.scope && states.rows.reduce((n, r) => n + r.count, 0) <= limit) return undefined;
        const result = await this.queryActivities((scope, rollup) =>
            this.activityFetch({ filter: base, orders, count: limit, columns: ["activityid", "createdon"] }, scope, rollup));
        const last = result.rows[result.rows.length - 1];
        return result.more && last ? date(last, "createdon") : undefined;
    }

    private inDateFilter(filters: TimelineFilters, value: Date): boolean {
        const f = filters.date;
        if (f.kind === "last") {
            const now = this.env.now().getTime();
            return value.getTime() >= now - f.days * 86400000 && value.getTime() <= now;
        }
        return true;
    }

    /** Details rows already loaded, by activity id, so a filter or sort shows them again without a query */
    private readonly detailRows = new Map<string, Row>();
    /** Attachment counts already counted, by activity id */
    private readonly attachmentCounts = new Map<string, number>();

    /** Forgets loaded details: all of them when the activities load again, or one item's after it's changed */
    private forgetDetails(id?: string): void {
        if (id === undefined) {
            this.detailRows.clear();
            this.attachmentCounts.clear();
        } else {
            this.detailRows.delete(id.toLowerCase());
            this.attachmentCounts.delete(id.toLowerCase());
        }
    }

    /** Bodies, participants and attachment counts for activities about to be shown: one query per 25 items not loaded yet */
    private async hydrate(items: TimelineItem[]): Promise<void> {
        const activities = items.filter((i) => i.kind === "activity");
        if (activities.length === 0) return;
        const missing = activities.filter((i) => {
            const row = this.detailRows.get(i.id.toLowerCase());
            if (row) this.applyDetails(i, row);
            return !row;
        });
        const byId = new Map(missing.map((i) => [i.id.toLowerCase(), i]));
        const chunks: TimelineItem[][] = [];
        for (let i = 0; i < missing.length; i += DETAILS_CHUNK) chunks.push(missing.slice(i, i + DETAILS_CHUNK));
        await Promise.all([
            ...chunks.map(async (chunk) => {
                const filter = chunk.map((i) => `activityid eq ${i.id}`).join(" or ");
                const result = await this.context.webAPI.retrieveMultipleRecords(
                    "activitypointer",
                    `?$select=activityid,description&$expand=${PARTY_EXPAND}&$filter=${filter}`,
                    chunk.length,
                );
                for (const r of result.entities as Row[]) {
                    const id = (str(r, "activityid") ?? "").toLowerCase();
                    this.detailRows.set(id, r);
                    const item = byId.get(id);
                    if (item) this.applyDetails(item, r);
                }
            }),
            this.addAttachmentCounts(activities),
            this.addStatusDetails(activities),
        ]);
    }

    /** The status reason beside the word on open items, from their table's metadata, cached per table */
    private async addStatusDetails(items: TimelineItem[]): Promise<void> {
        const open = items.filter((i) => isOpenState(i.state) && i.statusCode !== undefined);
        if (open.length === 0) return;
        const words = await this.getStateLabels();
        const entities = Array.from(new Set(open.map((i) => i.entity)));
        const options = new Map<string, StatusOption[]>();
        await Promise.all(entities.map(async (e) => options.set(e, withStatusDetails(statusOptions(await this.metadata(e, ["statuscode"])), words))));
        for (const item of open) item.statusDetail = options.get(item.entity)?.find((s) => s.value === item.statusCode)?.detail;
    }

    /** Appointments have no attachment count to read, so count theirs in one query per page; emails bring their own */
    private async addAttachmentCounts(items: TimelineItem[]): Promise<void> {
        const counted = (i: TimelineItem) => this.attachmentCounts.get(i.id.toLowerCase());
        const ids = items
            .filter((i) => (i.entity === "appointment" || (i.entity === "email" && i.attachmentCount === undefined)) && counted(i) === undefined)
            .map((i) => i.id);
        try {
            if (ids.length > 0) {
                const filter = ids.map((id) => `_objectid_value eq ${id}`).join(" or ");
                const result = await this.context.webAPI.retrieveMultipleRecords("activitymimeattachment", `?$select=_objectid_value&$filter=${filter}`, 5000);
                ids.forEach((id) => this.attachmentCounts.set(id.toLowerCase(), 0));
                for (const r of result.entities as Row[]) {
                    const id = str(r, "_objectid_value")?.toLowerCase();
                    if (id) this.attachmentCounts.set(id, (this.attachmentCounts.get(id) ?? 0) + 1);
                }
            }
        } catch {
            // Counts are a nicety; the feed works without them
        }
        items.forEach((i) => {
            const c = counted(i);
            if (c) i.attachmentCount = c;
        });
    }

    // --- mapping ------------------------------------------------------------------------------------------

    /** An activity from a light row; `sort` decides which date places it. Bodies and participants come from applyDetails. */
    private mapActivity(r: Row, sort: SortColumn): TimelineItem {
        const entity = str(r, "activitytypecode") ?? "activitypointer";
        const id = str(r, "activityid") ?? "";
        const state = mapState(num(r, "statecode"));
        const scheduledEnd = date(r, "scheduledend");
        const subject = str(r, "subject");
        const createdOn = date(r, "createdon") ?? new Date(0);

        const item: TimelineItem = {
            key: `${entity}:${id}`,
            id,
            entity,
            kind: "activity",
            typeLabel: formatted(r, "activitytypecode") ?? entity,
            title: subject ?? this.labels.untitled,
            date: createdOn,
            dateField: "createdon",
            createdOn,
            modifiedOn: date(r, "modifiedon"),
            scheduledStart: date(r, "scheduledstart"),
            scheduledEnd,
            actualEnd: date(r, "actualend"),
            durationMinutes: num(r, "actualdurationminutes"),
            state,
            // activitypointer labels status values generically (task "Not Started" = 2 = "Completed" there),
            // so the label comes from the activity's own table once the item is shown
            statusCode: num(r, "statuscode"),
            isOverdue: isOverdue(entity, state, scheduledEnd, this.env.now()),
            priority: mapPriority(num(r, "prioritycode")),
            priorityLabel: formatted(r, "prioritycode"),
            owner: lookup(r, "ownerid"),
            createdBy: lookup(r, "createdby"),
            from: [], to: [], cc: [], attendees: [],
            threadKey: entity === "email" ? threadKeyFor(subject) : undefined,
            attachmentCount: entity === "email" ? num(r, EMAIL_ATTACHMENTS) : undefined,
        };

        if (sort === "eventdate") {
            const placed = eventDate(item, dateRule(entity, this.config));
            item.date = placed.date;
            item.dateField = placed.field;
        } else {
            const value = date(r, sort);
            if (value) {
                item.date = value;
                item.dateField = sort;
            }
        }
        if ("description" in r || "activitypointer_activity_parties" in r) this.applyDetails(item, r);
        return item;
    }

    /** Body and participants, from a details query (or a full row) */
    private applyDetails(item: TimelineItem, r: Row): void {
        const description = str(r, "description");
        const isHtml = item.entity === "email" || looksLikeHtml(description);
        item.snippet = makeSnippet(description, isHtml);
        item.body = description;
        item.bodyIsHtml = isHtml;

        const from: PartyRef[] = [];
        const to: PartyRef[] = [];
        const cc: PartyRef[] = [];
        const attendees: PartyRef[] = [];
        const parties = (r.activitypointer_activity_parties as Row[] | undefined) ?? [];
        for (const p of parties) {
            const party: PartyRef = {
                id: str(p, "_partyid_value"),
                entity: str(p, `_partyid_value${LOOKUP_TYPE}`),
                name: formatted(p, "_partyid_value") ?? str(p, "addressused") ?? "",
                address: str(p, "addressused"),
            };
            if (!party.name) continue;
            switch (num(p, "participationtypemask")) {
                case 1: case 7: from.push(party); break;
                case 2: to.push(party); break;
                case 3: cc.push(party); break;
                case 5: case 6: attendees.push(party); break;
                case 11: if (to.length === 0) to.push(party); break;
            }
        }
        Object.assign(item, { from, to, cc, attendees });
        if ((item.entity === "email" || item.entity === "phonecall") && from.length > 0) {
            item.direction = from[0].entity && INTERNAL_PARTY_TYPES.has(from[0].entity) ? "out" : "in";
        }
    }

    private mapNote(r: Row, sortColumn: string): TimelineItem {
        const id = str(r, "annotationid") ?? "";
        const text = str(r, "notetext");
        const isHtml = looksLikeHtml(text);
        const fileName = r.isdocument === true ? str(r, "filename") : undefined;
        const heading = noteHeading(str(r, "subject"), fileName, makeSnippet(text, isHtml), this.labels.note);
        const createdBy = lookup(r, "createdby");
        return {
            key: `annotation:${id}`,
            id,
            entity: "annotation",
            kind: "note",
            typeLabel: this.labels.note,
            title: heading.title,
            noteSubject: str(r, "subject"),
            snippet: heading.snippet,
            body: text,
            bodyIsHtml: isHtml,
            date: date(r, sortColumn) ?? date(r, "createdon") ?? new Date(0),
            dateField: date(r, sortColumn) ? sortColumn : "createdon",
            createdOn: date(r, "createdon") ?? new Date(0),
            modifiedOn: date(r, "modifiedon"),
            state: "completed",
            isOverdue: false,
            owner: lookup(r, "ownerid"),
            createdBy,
            from: createdBy ? [createdBy] : [],
            to: [], cc: [], attendees: [],
            file: fileName ? { id, entity: "annotation", fileName, mimeType: str(r, "mimetype"), size: num(r, "filesize") } : undefined,
        };
    }

    public async getItem(entity: string, id: string): Promise<TimelineItem | undefined> {
        if (entity === "annotation") {
            const row = (await this.context.webAPI.retrieveRecord("annotation", id, `?$select=${NOTE_SELECT}`)) as Row;
            return this.mapNote(row, "createdon");
        }
        const result = await this.context.webAPI.retrieveMultipleRecords(
            "activitypointer",
            `?$select=${LIGHT_SELECT},description&$expand=${PARTY_EXPAND}&$filter=activityid eq ${normalizeId(id)}`,
            1,
        );
        const row = (result.entities as Row[])[0];
        if (!row) return undefined;
        const item = this.mapActivity(row, "createdon");
        await this.addStatusDetails([item]);
        return item;
    }

    // --- details ------------------------------------------------------------------------------------------

    private metadata(entity: string, attributes: string[]): Promise<MetadataLike | undefined> {
        const key = `${entity}|${attributes.join(",")}`;
        let cached = this.metadataCache.get(key);
        if (!cached) {
            cached = this.context.utils.getEntityMetadata(entity, attributes)
                .then((m) => m as MetadataLike)
                .catch(() => undefined);
            this.metadataCache.set(key, cached);
        }
        return cached;
    }

    public async getDetails(item: TimelineItem): Promise<ItemDetails> {
        if (item.kind === "note") {
            const text = item.body ?? "";
            return {
                fields: [],
                attachments: item.file ? [item.file] : [],
                edit: { title: item.noteSubject ?? "", text, textIsRich: !!item.bodyIsHtml, allDay: false, priorities: [] },
            };
        }
        const attachmentsPromise = this.getAttachments(item.id);
        const columns = previewColumns(item.entity, this.config);
        const open = canEdit(item);
        // What the preview can change comes along in the same query, so being able to work on an item costs nothing extra
        const editing = open && quickEdit(item.entity) !== undefined;
        const editColumns = editing ? ["subject", "description", "scheduledstart", "scheduledend", "prioritycode", ...(item.entity === "appointment" ? ["isalldayevent"] : [])] : [];
        const asked = open ? Array.from(new Set([...columns, "prioritycode", "statuscode"])) : columns;
        const md = asked.length > 0 ? await this.metadata(item.entity, asked) : undefined;
        const valid = columns.filter((c) => !md?.Attributes?.get || md.Attributes.get(c) !== undefined);
        const names = valid.map((c) => (isLookupAttribute(md?.Attributes?.get?.(c)) ? `_${c}_value` : c));
        const select = Array.from(new Set([...names, ...editColumns]));
        const fields: PreviewField[] = [];
        let edit: EditValues | undefined;
        if (select.length > 0) {
            try {
                const row = (await this.context.webAPI.retrieveRecord(item.entity, item.id, `?$select=${select.join(",")}`)) as Row;
                valid.forEach((col, i) => {
                    const value = this.displayValue(row, names[i]);
                    if (value !== undefined) {
                        fields.push({ name: col, label: md?.Attributes?.get?.(col)?.DisplayName ?? col, value });
                    }
                });
                if (editing) edit = this.editValues(row, md);
            } catch {
                // A misconfigured column shouldn't break the preview; the rest still renders
            }
        }
        return { fields, attachments: await attachmentsPromise, edit, statuses: open ? withStatusDetails(statusOptions(md), await this.getStateLabels()) : undefined };
    }

    private editValues(row: Row, md: MetadataLike | undefined): EditValues {
        const options = md?.Attributes?.get?.("prioritycode")?.OptionSet ?? {};
        const text = str(row, "description") ?? "";
        return {
            title: str(row, "subject") ?? "",
            text,
            textIsRich: looksLikeHtml(text),
            start: date(row, "scheduledstart"),
            end: date(row, "scheduledend"),
            allDay: row.isalldayevent === true,
            priority: num(row, "prioritycode"),
            priorities: Object.keys(options).map((value) => ({ value: Number(value), label: options[value]?.text ?? value })),
        };
    }

    private displayValue(row: Row, key: string): string | undefined {
        const f = formatted(row, key);
        if (f !== undefined) return f;
        const v = row[key];
        if (v === null || v === undefined || v === "") return undefined;
        if (typeof v === "string" && /^\d{4}-\d{2}-\d{2}T/.test(v)) {
            const d = new Date(v);
            return isNaN(d.getTime()) ? v : formatFull(this.env, d);
        }
        if (typeof v === "string" || typeof v === "number" || typeof v === "boolean") return String(v);
        return undefined;
    }

    private async getAttachments(activityId: string): Promise<AttachmentRef[]> {
        try {
            const result = await this.context.webAPI.retrieveMultipleRecords(
                "activitymimeattachment",
                `?$select=activitymimeattachmentid,filename,filesize,mimetype,attachmentcontentid&$filter=_objectid_value eq ${activityId}`,
                100,
            );
            return (result.entities as Row[]).map((r) => ({
                id: str(r, "activitymimeattachmentid") ?? "",
                entity: "activitymimeattachment",
                fileName: str(r, "filename") ?? "file",
                mimeType: str(r, "mimetype"),
                size: num(r, "filesize"),
                contentId: str(r, "attachmentcontentid"),
            }));
        } catch {
            return [];
        }
    }

    public async getFileContent(file: AttachmentRef): Promise<FileContent> {
        const column = file.entity === "annotation" ? "documentbody" : "body";
        const row = (await this.context.webAPI.retrieveRecord(file.entity, file.id, `?$select=${column},mimetype,filename`)) as Row;
        return { base64: str(row, column) ?? "", mimeType: str(row, "mimetype") ?? file.mimeType, fileName: str(row, "filename") ?? file.fileName };
    }

    public async getTypeLabels(entities: string[]): Promise<ActivityTypeInfo[]> {
        return Promise.all(
            entities.map(async (entity) => {
                if (entity === "annotation") return { entity, label: this.labels.note };
                const md = await this.metadata(entity, []);
                return { entity, label: md?.DisplayName ?? entity };
            }),
        );
    }

    /** Every activity shares this one list, whatever its own status reasons are called, and Dataverse translates it */
    public async getStateLabels(): Promise<StateLabels> {
        const options = (await this.metadata("activitypointer", ["statecode"]))?.Attributes?.get?.("statecode")?.OptionSet;
        return { open: options?.["0"]?.text, completed: options?.["1"]?.text, canceled: options?.["2"]?.text, scheduled: options?.["3"]?.text };
    }

    // --- actions ------------------------------------------------------------------------------------------

    public async createNote(note: NewNote): Promise<void> {
        const md = await this.metadata(this.record.entity, []);
        const entitySet = md?.EntitySetName;
        if (!entitySet) throw new Error(`Couldn't find the entity set for ${this.record.entity}.`);
        const data: Row = {
            notetext: note.text,
            [`objectid_${this.record.entity}@odata.bind`]: `/${entitySet}(${normalizeId(this.record.id)})`,
        };
        if (note.title) data.subject = note.title;
        if (note.file) {
            data.filename = note.file.name;
            data.mimetype = note.file.type || "application/octet-stream";
            data.documentbody = await readAsBase64(note.file);
            data.isdocument = true;
        }
        await this.context.webAPI.createRecord("annotation", data);
    }

    public async completeActivity(item: TimelineItem): Promise<void> {
        if (!canComplete(item.entity)) return;
        // Without a status reason, Dataverse sets the table's default for the new state
        await this.context.webAPI.updateRecord(item.entity, item.id, { statecode: 1 });
    }

    public async updateItem(item: TimelineItem, before: EditValues, changes: ItemChanges): Promise<void> {
        const data: Row = {};
        if (changes.title !== undefined) data.subject = changes.title;
        if (changes.text !== undefined) data[item.kind === "note" ? "notetext" : "description"] = changes.text;
        if (changes.start !== undefined) data.scheduledstart = changes.start?.toISOString() ?? null;
        if (changes.end !== undefined) data.scheduledend = changes.end?.toISOString() ?? null;
        if (changes.priority !== undefined) data.prioritycode = changes.priority;
        if (changes.status) {
            data.statecode = changes.status.state;
            // Closing leaves the status reason to Dataverse, as completing does
            if (isOpenState(mapState(changes.status.state))) data.statuscode = changes.status.value;
        }
        await this.context.webAPI.updateRecord(item.entity, item.id, data);
        applyChanges(item, before, changes, this.labels.note, this.env.now());
        // The snapshot and the loaded details still hold the item as it was; the next feed loads them again
        this.snapshotPromise = undefined;
        this.forgetDetails(item.id);
    }

    public async openRecord(entity: string, id: string): Promise<void> {
        await this.context.navigation.openForm({ entityName: entity, entityId: id });
    }

    public async openRecordPanel(entity: string, id: string): Promise<void> {
        // The PCF API has no panel, so this is the app's own navigation. Other hosts don't have it and open the record instead.
        const navigation = (window as unknown as XrmWindow).Xrm?.Navigation;
        if (!navigation?.navigateTo) {
            await this.openRecord(entity, id);
            return;
        }
        await navigation.navigateTo(
            { pageType: "entityrecord", entityName: entity, entityId: id, formType: 2 },
            { target: 2, position: 2, width: { value: PREVIEW_WIDTH, unit: "px" } },
        );
    }

    public async createActivity(entity: string): Promise<boolean> {
        const result = await this.context.navigation.openForm({
            entityName: entity,
            useQuickCreateForm: entity !== "email",
            createFromEntity: { entityType: this.record.entity, id: normalizeId(this.record.id), name: this.record.name },
        });
        const saved = (result as { savedEntityReference?: unknown[] } | undefined)?.savedEntityReference;
        // Main forms resolve without a reference; refresh anyway in that case
        return !saved || saved.length > 0;
    }

    public recordUrl(entity: string, id: string): string | undefined {
        if (typeof window === "undefined") return undefined;
        const appId = new URLSearchParams(window.location.search).get("appid");
        return `${window.location.origin}/main.aspx?${appId ? `appid=${appId}&` : ""}pagetype=entityrecord&etn=${entity}&id=${id}`;
    }
}

/** Open work can be set to each of its status reasons. Closing is one choice per state, and Dataverse picks the reason when it's saved. */
function statusOptions(md: MetadataLike | undefined): StatusOption[] {
    const options = (md?.Attributes?.get?.("statuscode")?.attributeDescriptor?.OptionSet ?? []).flatMap((o) =>
        !o.IsHidden && o.Value !== undefined && o.State !== undefined ? [{ value: o.Value, state: o.State, label: o.Label ?? "" }] : [],
    );
    return options.filter((s, i) => isOpenState(mapState(s.state)) || options.findIndex((o) => o.state === s.state) === i);
}

function isOverdue(entity: string, state: ItemState, scheduledEnd: Date | undefined, now: Date): boolean {
    return entity !== "email" && (state === "open" || state === "scheduled") && !!scheduledEnd && scheduledEnd.getTime() < now.getTime();
}

/** Counts per type and state from snapshot rows, as the aggregate query gives them */
function countRows(rows: Row[]): TypeStates["rows"] {
    const counts = new Map<string, TypeStates["rows"][number]>();
    for (const r of rows) {
        const entity = str(r, "activitytypecode") ?? "activitypointer";
        const open = isOpenState(mapState(num(r, "statecode")));
        const key = `${entity}:${open}`;
        const entry = counts.get(key) ?? { entity, label: formatted(r, "activitytypecode") ?? entity, open, count: 0 };
        entry.count++;
        counts.set(key, entry);
    }
    return Array.from(counts.values());
}

function countOverdueRows(rows: Row[], now: Date): number {
    return rows.filter((r) => isOverdue(str(r, "activitytypecode") ?? "", mapState(num(r, "statecode")), date(r, "scheduledend"), now)).length;
}

/** The status filter, as statusCondition puts it in FetchXML */
function matchesStatus(item: TimelineItem, status: TimelineFilters["status"]): boolean {
    switch (status) {
        case "open": return isOpenState(item.state);
        case "completed": return item.state === "completed";
        case "overdue": return item.isOverdue;
        default: return true;
    }
}

/** One page of items held in memory; the cursor is where the page starts */
function pageOf(items: TimelineItem[], cursor: string | undefined, size: number): StreamPage {
    const from = cursor ? Number(cursor) : 0;
    const to = from + size;
    return { items: items.slice(from, to), next: to < items.length ? String(to) : undefined };
}

function readSessionFlag(key: string): boolean {
    try {
        return window.sessionStorage.getItem(key) !== null;
    } catch {
        return false;
    }
}

function writeSessionFlag(key: string): void {
    try {
        window.sessionStorage.setItem(key, "1");
    } catch {
        // Without storage, a large record just tries the single query again next time
    }
}

/** Turns an absolute @odata.nextLink into the options string retrieveMultipleRecords expects */
function nextOptions(nextLink: string | undefined): string | undefined {
    if (!nextLink) return undefined;
    const q = nextLink.indexOf("?");
    return q >= 0 ? nextLink.substring(q) : undefined;
}

function readAsBase64(file: File): Promise<string> {
    return new Promise((resolve, reject) => {
        const reader = new FileReader();
        reader.onload = () => {
            const result = typeof reader.result === "string" ? reader.result : "";
            resolve(result.substring(result.indexOf(",") + 1));
        };
        reader.onerror = () => reject(reader.error ?? new Error("Couldn't read the file."));
        reader.readAsDataURL(file);
    });
}
