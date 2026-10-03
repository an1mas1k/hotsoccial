const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const https = require('https');
const { parse: parseUrl } = require('url');

const PORT = process.env.PORT || 3000;
const USERS_FILE = path.join(__dirname, 'users.json');
const POSTS_FILE = path.join(__dirname, 'posts.json');
const DM_FILE = path.join(__dirname, 'dm.json');
const CHANNELS_FILE = path.join(__dirname, 'channels.json');
const CHATS_FILE = path.join(__dirname, 'chats.json');
const SESSIONS_FILE = path.join(__dirname, 'sessions.json');
const HTML_FILE = path.join(__dirname, 'index.html');
const UPLOAD_DIR = path.join(__dirname, 'uploads');
try { fs.mkdirSync(UPLOAD_DIR, { recursive: true }); } catch (e) {}

const MAX_BODY_SIZE = 30 * 1024 * 1024;       // только для маршрутов с загрузкой файлов
const DEFAULT_BODY_SIZE = 256 * 1024;          // для всех остальных запросов
const MAX_ATTACH_SIZE = 20 * 1024 * 1024;
const VIDEO_EXT = { 'video/mp4': 'mp4', 'video/webm': 'webm', 'video/quicktime': 'mov', 'video/ogg': 'ogv', 'video/x-m4v': 'm4v' };
const VIDEO_MIME = { mp4: 'video/mp4', webm: 'video/webm', mov: 'video/quicktime', ogv: 'video/ogg', m4v: 'video/mp4' };
const IMAGE_MIME = { png: 'image/png', jpg: 'image/jpeg', jpeg: 'image/jpeg', webp: 'image/webp', gif: 'image/gif' };
const POSTS_PER_WALL = 100;
const FEED_LIMIT = 100;
const DM_HISTORY_LIMIT = 300;
const HANDLE_RE = /^[a-zA-Z0-9_]{3,20}$/;
const IMAGE_DATA_RE = /^data:image\/(png|jpeg|jpg|webp|gif);base64,/i;
const IMAGE_EXT = { png: 'png', jpeg: 'jpg', jpg: 'jpg', webp: 'webp', gif: 'gif' };
const MAX_IMAGE_SIZE = 5 * 1024 * 1024;
const RATE_WINDOW_MS = 10 * 60 * 1000;
const LOGIN_MAX_ATTEMPTS = 8;
const REGISTER_MAX_ATTEMPTS = 12;
const rateBuckets = new Map();
const SESSION_TTL = 30 * 24 * 60 * 60 * 1000; // 30 дней

// OAuth settings. Set these environment variables before starting the server.
const GOOGLE_CLIENT_ID = process.env.GOOGLE_CLIENT_ID || '240353019911-kqidnu791scvkfq4f93sdoull23eonnk.apps.googleusercontent.com';

const callSignals = {};
const CALL_TYPES = ['offer', 'answer', 'candidate', 'hangup', 'decline', 'busy'];
function pushCallSignal(toUser, signal) {
    const key = toUser.toLowerCase();
    const q = callSignals[key] || (callSignals[key] = []);
    q.push(signal);
    if (q.length > 200) q.splice(0, q.length - 200);
}
function popCallSignals(user) {
    const key = user.toLowerCase();
    const now = Date.now();
    const signals = (callSignals[key] || []).filter(s => now - s.time < 90000);
    delete callSignals[key];
    return signals;
}

function ensureFile(filePath) { if (!fs.existsSync(filePath)) fs.writeFileSync(filePath, '[]', 'utf8'); }
[USERS_FILE, POSTS_FILE, DM_FILE, CHANNELS_FILE, CHATS_FILE, SESSIONS_FILE].forEach(ensureFile);

function readJSON(fp) {
    let raw = '';
    try { raw = fs.readFileSync(fp, 'utf8'); } catch (e) { return []; }
    try { return JSON.parse(raw || '[]'); }
    catch (e) {
        // файл повреждён: сохраняем копию, чтобы данные не пропали при следующей записи
        try { fs.copyFileSync(fp, fp + '.corrupt-' + Date.now()); } catch (e2) {}
        console.error('Повреждён файл ' + path.basename(fp) + ', копия сохранена рядом');
        return [];
    }
}
function writeJSON(fp, data) {
    // атомарная запись: сначала во временный файл, потом переименование
    const tmp = fp + '.tmp';
    fs.writeFileSync(tmp, JSON.stringify(data, null, 2), 'utf8');
    fs.renameSync(tmp, fp);
}

function readUsers() { return readJSON(USERS_FILE); }
function saveUsers(u) { writeJSON(USERS_FILE, u); }
function readPosts() { return readJSON(POSTS_FILE); }
function savePosts(p) { writeJSON(POSTS_FILE, p); }
function readDms() { return readJSON(DM_FILE); }
function saveDms(d) { writeJSON(DM_FILE, d); }
function readChannels() { return readJSON(CHANNELS_FILE); }
function saveChannels(c) { writeJSON(CHANNELS_FILE, c); }
function readChats() { return readJSON(CHATS_FILE); }
function saveChats(c) { writeJSON(CHATS_FILE, c); }
function readSessions() { return readJSON(SESSIONS_FILE); }
function saveSessions(s) { writeJSON(SESSIONS_FILE, s); }

function normalizeHandle(raw) { return (raw || '').trim().replace(/^@+/, ''); }
function dmKey(a, b) { return [String(a).toLowerCase(), String(b).toLowerCase()].sort().join('::'); }
/* ========== ВЛОЖЕНИЯ (видео и файлы) ========== */
function saveImageData(dataUrl) {
    if (typeof dataUrl !== 'string' || !IMAGE_DATA_RE.test(dataUrl)) return null;
    const m = IMAGE_DATA_RE.exec(dataUrl);
    const mime = (m[1] || '').toLowerCase();
    const ext = IMAGE_EXT[mime];
    if (!ext) return null;
    const encoded = dataUrl.slice(m[0].length);
    let buf;
    try { buf = Buffer.from(encoded, 'base64'); } catch (e) { return null; }
    if (!buf.length || buf.length > MAX_IMAGE_SIZE) return null;
    // Basic magic-byte validation so a data:image label cannot hide arbitrary content.
    const signatures = {
        png: buf.length >= 8 && buf.slice(0, 8).equals(Buffer.from([0x89,0x50,0x4e,0x47,0x0d,0x0a,0x1a,0x0a])),
        jpg: buf.length >= 3 && buf.slice(0, 3).equals(Buffer.from([0xff,0xd8,0xff])),
        webp: buf.length >= 12 && buf.slice(0, 4).toString('ascii') === 'RIFF' && buf.slice(8, 12).toString('ascii') === 'WEBP',
        gif: buf.length >= 6 && (buf.slice(0, 6).toString('ascii') === 'GIF87a' || buf.slice(0, 6).toString('ascii') === 'GIF89a')
    };
    if (!signatures[ext]) return null;
    const name = crypto.randomBytes(16).toString('hex') + '.' + ext;
    try { fs.writeFileSync(path.join(UPLOAD_DIR, name), buf); } catch (e) { return null; }
    return '/uploads/' + name;
}

function isStoredImageUrl(value) {
    return typeof value === 'string' && /^\/uploads\/[a-f0-9]{32}\.(?:png|jpg|webp|gif)$/i.test(value);
}

function processImageInput(value, allowEmpty) {
    if (value === '' && allowEmpty) return '';
    if (typeof value !== 'string') return null;
    if (isStoredImageUrl(value)) return value;
    return saveImageData(value);
}

function rateLimit(req, bucket, maxAttempts, idOverride) {
    const ip = idOverride ? String(idOverride).toLowerCase() : String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || 'unknown').split(',')[0].trim();
    const now = Date.now();
    const key = bucket + ':' + ip;
    let item = rateBuckets.get(key);
    if (!item || now - item.startedAt >= RATE_WINDOW_MS) {
        item = { startedAt: now, count: 0 };
        rateBuckets.set(key, item);
    }
    item.count++;
    if (item.count > maxAttempts) {
        return Math.max(1, Math.ceil((RATE_WINDOW_MS - (now - item.startedAt)) / 1000));
    }
    if (rateBuckets.size > 2000) {
        for (const [k, v] of rateBuckets) if (now - v.startedAt >= RATE_WINDOW_MS) rateBuckets.delete(k);
    }
    return 0;
}

function saveAttachment(dataUrl, kind, origName) {
    if (typeof dataUrl !== 'string') return null;
    const m = /^data:([^;,]*)[^,]*;base64,/.exec(dataUrl);
    if (!m) return null;
    const mime = (m[1] || '').toLowerCase();
    let ext = '';
    if (kind === 'video') {
        ext = VIDEO_EXT[mime];
        if (!ext) return null;
    } else {
        const em = /\.([a-zA-Z0-9]{1,8})$/.exec(origName || '');
        ext = em ? em[1].toLowerCase() : '';
    }
    const buf = Buffer.from(dataUrl.slice(m[0].length), 'base64');
    if (!buf.length || buf.length > MAX_ATTACH_SIZE) return null;
    if (kind === 'video') {
        const head4 = buf.slice(0, 4);
        const okMagic = (ext === 'webm' && head4.equals(Buffer.from([0x1a, 0x45, 0xdf, 0xa3])))
            || (ext === 'ogv' && head4.toString('ascii') === 'OggS')
            || (['mp4', 'mov', 'm4v'].includes(ext) && buf.length > 12 && buf.slice(4, 8).toString('ascii') === 'ftyp');
        if (!okMagic) return null;
    }
    const name = crypto.randomBytes(16).toString('hex') + (ext ? '.' + ext : '');
    try { fs.writeFileSync(path.join(UPLOAD_DIR, name), buf); } catch (e) { return null; }
    return { url: '/uploads/' + name, size: buf.length };
}
function serveUpload(req, res, url) {
    const name = path.basename(url.slice('/uploads/'.length));
    if (!/^[a-f0-9]{32}(\.[a-z0-9]{1,8})?$/.test(name)) return sendJSON(res, 404, { error: 'Не найдено' });
    const fp = path.join(UPLOAD_DIR, name);
    fs.stat(fp, (err, st) => {
        if (err || !st.isFile()) return sendJSON(res, 404, { error: 'Не найдено' });
        const ext = path.extname(name).slice(1).toLowerCase();
        const isVideo = !!VIDEO_MIME[ext];
        const isImage = !!IMAGE_MIME[ext];
        const headers = {
            'Content-Type': isVideo ? VIDEO_MIME[ext] : (isImage ? IMAGE_MIME[ext] : 'application/octet-stream'),
            'Accept-Ranges': 'bytes',
            'X-Content-Type-Options': 'nosniff',
            'Cache-Control': 'public, max-age=31536000, immutable'
        };
        if (!isVideo && !isImage) headers['Content-Disposition'] = 'attachment';
        const range = req.headers.range;
        if (range) {
            const r = /bytes=(\d*)-(\d*)/.exec(range);
            let start = r && r[1] ? parseInt(r[1], 10) : 0;
            let end = r && r[2] ? parseInt(r[2], 10) : st.size - 1;
            if (isNaN(start) || isNaN(end) || start > end || start >= st.size) {
                res.writeHead(416, { 'Content-Range': 'bytes */' + st.size });
                return res.end();
            }
            end = Math.min(end, st.size - 1);
            headers['Content-Range'] = 'bytes ' + start + '-' + end + '/' + st.size;
            headers['Content-Length'] = end - start + 1;
            res.writeHead(206, headers);
            fs.createReadStream(fp, { start, end }).pipe(res);
        } else {
            headers['Content-Length'] = st.size;
            res.writeHead(200, headers);
            fs.createReadStream(fp).pipe(res);
        }
    });
}

/* ========== КУЛДАУН СООБЩЕНИЙ ========== */
const MSG_COOLDOWN_MS = 500;
const msgLastSent = new Map();
function msgCooldown(username) {
    const key = String(username).toLowerCase();
    const now = Date.now();
    const wait = MSG_COOLDOWN_MS - (now - (msgLastSent.get(key) || 0));
    if (wait > 0) return wait;
    msgLastSent.set(key, now);
    if (msgLastSent.size > 5000) { for (const [k, v] of msgLastSent) if (now - v > 60000) msgLastSent.delete(k); }
    return 0;
}
function cooldownReply(res, waitMs) {
    return sendJSON(res, 429, { error: 'Не так быстро, подожди полсекунды', retryAfterMs: waitMs });
}

function makeId() { return Date.now().toString(36) + Math.random().toString(36).slice(2, 8); }

const failBuckets = new Map();
function loginLocked(key) {
    const it = failBuckets.get(key);
    if (!it) return false;
    if (Date.now() - it.startedAt >= RATE_WINDOW_MS) { failBuckets.delete(key); return false; }
    return it.count >= 10;
}
function noteLoginFail(key) {
    const it = failBuckets.get(key);
    if (!it || Date.now() - it.startedAt >= RATE_WINDOW_MS) failBuckets.set(key, { startedAt: Date.now(), count: 1 });
    else it.count++;
    if (failBuckets.size > 5000) { const now = Date.now(); for (const [k, v] of failBuckets) if (now - v.startedAt >= RATE_WINDOW_MS) failBuckets.delete(k); }
}
function safeEqualHex(a, b) {
    const x = Buffer.from(String(a), 'utf8'), y = Buffer.from(String(b), 'utf8');
    return x.length === y.length && crypto.timingSafeEqual(x, y);
}
function hashPassword(password, salt) {
    return crypto.scryptSync(password, salt, 64).toString('hex');
}
function generateSalt() { return crypto.randomBytes(16).toString('hex'); }
function generateToken() { return crypto.randomBytes(32).toString('hex'); }

function createSession(username) {
    const sessions = readSessions().filter(s => Date.now() - s.createdAt < SESSION_TTL);
    const token = generateToken();
    sessions.push({ token, username, createdAt: Date.now() });
    saveSessions(sessions);
    return token;
}
function getSessionUser(token) {
    if (!token) return null;
    const sessions = readSessions();
    const s = sessions.find(x => x.token === token);
    if (!s) return null;
    if (Date.now() - s.createdAt > SESSION_TTL) return null;
    const users = readUsers();
    return users.find(u => u.username.toLowerCase() === s.username.toLowerCase()) || null;
}
function destroySession(token) {
    if (!token) return;
    const sessions = readSessions().filter(s => s.token !== token);
    saveSessions(sessions);
}
function destroyUserSessions(username) {
    const sessions = readSessions().filter(s => s.username.toLowerCase() !== username.toLowerCase());
    saveSessions(sessions);
}

function sendJSON(res, status, data) {
    res.writeHead(status, {
        'X-Content-Type-Options': 'nosniff',
        'Cache-Control': 'no-store',
        'Content-Type': 'application/json; charset=utf-8',
        'Access-Control-Allow-Origin': '*',
        'Access-Control-Allow-Headers': 'Content-Type, Authorization',
        'Access-Control-Allow-Methods': 'GET, POST, DELETE, OPTIONS'
    });
    res.end(JSON.stringify(data));
}
function readBody(req, maxBytes) {
    const limit = maxBytes || DEFAULT_BODY_SIZE;
    return new Promise(function (resolve, reject) {
        const chunks = [];
        let size = 0, dead = false;
        req.on('data', function (chunk) {
            if (dead) return;
            size += chunk.length;
            if (size > limit) { dead = true; reject(new Error('Слишком большой запрос')); req.destroy(); return; }
            chunks.push(chunk);
        });
        req.on('end', function () {
            if (dead) return;
            try {
                const body = Buffer.concat(chunks).toString('utf8');
                resolve(body ? JSON.parse(body) : {});
            } catch (e) { reject(new Error('Некорректный JSON')); }
        });
        req.on('error', function (e) { if (!dead) reject(e); });
    });
}
function getToken(req) {
    const auth = req.headers['authorization'] || '';
    if (auth.startsWith('Bearer ')) return auth.slice(7);
    return null;
}
// Возвращает пользователя по токену, или null
function authUser(req) {
    return getSessionUser(getToken(req));
}

/* ========== AUTH ========== */

async function handleRegister(req, res) {
    try {
        const retry = rateLimit(req, 'register', REGISTER_MAX_ATTEMPTS);
        if (retry) return sendJSON(res, 429, { error: 'Слишком много попыток регистрации', retryAfter: retry });
        const data = await readBody(req);
        const username = (data.username || '').trim();
        const email = (data.email || '').trim().replace(/[\s\u00A0\u200B\uFEFF]/g, '');
        const password = data.password || '';
        if (!HANDLE_RE.test(username)) return sendJSON(res, 400, { error: 'Ник: 3-20 символов, только латиница, цифры и _' });
        if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email)) return sendJSON(res, 400, { error: 'Некорректный email' });
        if (data.acceptedPrivacy !== true) return sendJSON(res, 400, { error: 'Нужно принять политику конфиденциальности' });
        if (password.length < 6) return sendJSON(res, 400, { error: 'Пароль — минимум 6 символов' });
        if (password.length > 200) return sendJSON(res, 400, { error: 'Пароль слишком длинный' });
        const users = readUsers();
        if (users.some(u => u.username.toLowerCase() === username.toLowerCase())) return sendJSON(res, 409, { error: 'Такое имя уже занято' });
        if (users.some(u => u.email.toLowerCase() === email.toLowerCase())) return sendJSON(res, 409, { error: 'Эта почта уже зарегистрирована' });
        const salt = generateSalt();
        const newUser = {
            username, email, salt,
            passwordHash: hashPassword(password, salt),
            avatar: '', handle: '', theme: 'dark', wallpaper: '', birthday: '',
            friends: [], incomingRequests: [], blocked: [],
            privacyAcceptedAt: new Date().toISOString(), privacyVersion: '2026-10-03',
            createdAt: new Date().toISOString(), lastSeen: new Date().toISOString()
        };
        users.push(newUser);
        saveUsers(users);
        const token = createSession(newUser.username);
        sendJSON(res, 201, {
            token,
            user: {
                username: newUser.username, email: newUser.email, avatar: '', handle: '',
                theme: 'dark', wallpaper: '', birthday: '',
                friends: [], incomingRequests: [], blocked: []
            }
        });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}

async function handleLogin(req, res) {
    try {
        const retry = rateLimit(req, 'login', LOGIN_MAX_ATTEMPTS);
        if (retry) return sendJSON(res, 429, { error: 'Слишком много попыток входа', retryAfter: retry });
        const data = await readBody(req);
        const login = (data.login || '').trim().toLowerCase();
        const password = data.password || '';
        if (!login || !password) return sendJSON(res, 400, { error: 'Введите логин и пароль' });
        const users = readUsers();
        if (password.length > 200) return sendJSON(res, 400, { error: 'Пароль слишком длинный' });
        if (loginLocked(login)) return sendJSON(res, 429, { error: 'Слишком много неверных попыток для этого аккаунта, подожди 10 минут' });
        const user = users.find(u => u.username.toLowerCase() === login || u.email.toLowerCase() === login);
        if (!user || !user.passwordHash) {
            hashPassword(password, 'dummy-salt-for-timing');
            noteLoginFail(login);
            return sendJSON(res, 401, { error: 'Неверный логин или пароль' });
        }
        if (!safeEqualHex(hashPassword(password, user.salt), user.passwordHash)) {
            noteLoginFail(login);
            return sendJSON(res, 401, { error: 'Неверный логин или пароль' });
        }
        failBuckets.delete(login);
        user.lastSeen = new Date().toISOString();
        saveUsers(users);
        const token = createSession(user.username);
        sendJSON(res, 200, {
            token,
            user: {
                username: user.username, email: user.email, avatar: user.avatar || '',
                handle: user.handle || '', theme: user.theme || 'dark',
                wallpaper: user.wallpaper || '', birthday: user.birthday || '',
                friends: user.friends || [], incomingRequests: user.incomingRequests || [],
                blocked: user.blocked || []
            }
        });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}

// Восстановление сессии по токену
function httpsJson(options, body) {
    return new Promise(function (resolve, reject) {
        const req = https.request(options, function (response) {
            let data = '';
            response.setEncoding('utf8');
            response.on('data', function (chunk) { data += chunk; });
            response.on('end', function () {
                let json = null;
                try { json = JSON.parse(data || '{}'); } catch (e) {}
                if (response.statusCode < 200 || response.statusCode >= 300) {
                    const msg = json && (json.error_description || json.error || json.message);
                    return reject(new Error(msg || ('HTTP ' + response.statusCode)));
                }
                resolve(json || {});
            });
        });
        req.setTimeout(10000, function () { req.destroy(new Error('OAuth request timeout')); });
        req.on('error', reject);
        if (body) req.write(body);
        req.end();
    });
}

function oauthUsername(name, email, users) {
    let base = String(name || '').trim().toLowerCase()
        .replace(/[^a-z0-9_]+/gi, '_')
        .replace(/^_+|_+$/g, '')
        .slice(0, 16);
    if (!base) {
        base = String(email || 'user').split('@')[0]
            .toLowerCase().replace(/[^a-z0-9_]+/gi, '_').replace(/^_+|_+$/g, '').slice(0, 16) || 'user';
    }
    if (base.length < 3) base = (base + '_user').slice(0, 20);
    let candidate = base;
    let n = 1;
    while (users.some(function (u) { return String(u.username || '').toLowerCase() === candidate.toLowerCase(); })) {
        const suffix = '_' + n++;
        candidate = base.slice(0, Math.max(3, 20 - suffix.length)) + suffix;
    }
    return candidate;
}

function publicUser(user) {
    return {
        username: user.username, email: user.email, avatar: user.avatar || '',
        handle: user.handle || '', theme: user.theme || 'dark',
        wallpaper: user.wallpaper || '', birthday: user.birthday || '',
        friends: user.friends || [], incomingRequests: user.incomingRequests || [],
        blocked: user.blocked || []
    };
}

function loginOrCreateSocialUser(provider, providerId, profile) {
    const users = readUsers();
    const id = String(providerId || '').trim();
    const email = String(profile.email || '').trim().toLowerCase();
    if (!id) throw new Error('OAuth provider did not return a user id');
    let user = users.find(function (u) { return String(u[provider + 'Id'] || '') === id; });
    if (!user && email) {
        const emailMatch = users.find(function (u) { return String(u.email || '').toLowerCase() === email; });
        if (emailMatch) {
            // Never attach OAuth to a password account just because the email string matches.
            // Linking must be an explicit authenticated action.
            if (emailMatch.passwordHash) throw new Error('Google-аккаунт не привязан к этому профилю');
            user = emailMatch;
        }
    }

    if (!user) {
        user = {
            username: oauthUsername(profile.name || profile.firstName || 'user', email, users),
            email: email || (provider + '_' + id + '@oauth.local'),
            salt: '', passwordHash: '',
            avatar: profile.avatar || '', handle: '', theme: 'dark', wallpaper: '', birthday: '',
            friends: [], incomingRequests: [], blocked: [],
            createdAt: new Date().toISOString(), lastSeen: new Date().toISOString()
        };
        user[provider + 'Id'] = id;
        users.push(user);
    } else {
        user[provider + 'Id'] = id;
        if (!user.avatar && profile.avatar) user.avatar = profile.avatar;
        if (profile.email && !user.email) user.email = profile.email;
        user.lastSeen = new Date().toISOString();
    }
    saveUsers(users);
    const token = createSession(user.username);
    return { token, user: publicUser(user) };
}

async function handleGoogleAuth(req, res) {
    try {
        const data = await readBody(req);
        const credential = String(data.credential || '').trim();
        if (!credential) return sendJSON(res, 400, { error: 'Google не передал ID token' });
        if (!GOOGLE_CLIENT_ID || GOOGLE_CLIENT_ID.indexOf('PASTE_') === 0) {
            return sendJSON(res, 503, { error: 'На сервере не настроен GOOGLE_CLIENT_ID' });
        }

        // Для локальной разработки: Google tokeninfo проверяет подпись/issuer/expiry.
        // Для production Google рекомендует google-auth-library и локальную проверку JWK.
        const info = await httpsJson({
            hostname: 'oauth2.googleapis.com',
            path: '/tokeninfo?id_token=' + encodeURIComponent(credential),
            method: 'GET',
            headers: { 'Accept': 'application/json' }
        });
        if (info.iss !== 'https://accounts.google.com' && info.iss !== 'accounts.google.com') {
            return sendJSON(res, 401, { error: 'Недействительный Google ID token' });
        }
        if (String(info.aud || '') !== GOOGLE_CLIENT_ID) {
            return sendJSON(res, 401, { error: 'Google Client ID не совпадает' });
        }
        if (String(info.email_verified) !== 'true') {
            return sendJSON(res, 401, { error: 'Google email не подтверждён' });
        }
        const result = loginOrCreateSocialUser('google', info.sub, {
            name: info.name || info.email,
            email: info.email,
            avatar: info.picture || ''
        });
        sendJSON(res, 200, result);
    } catch (e) {
        sendJSON(res, 401, { error: 'Ошибка авторизации Google: ' + (e.message || 'неизвестная ошибка') });
    }
}

function handleSession(req, res) {
    const token = getToken(req);
    const user = getSessionUser(token);
    if (!user) return sendJSON(res, 401, { error: 'Сессия истекла' });
    sendJSON(res, 200, {
        token,
        user: {
            username: user.username, email: user.email, avatar: user.avatar || '',
            handle: user.handle || '', theme: user.theme || 'dark',
            wallpaper: user.wallpaper || '', birthday: user.birthday || '',
            friends: user.friends || [], incomingRequests: user.incomingRequests || [],
            blocked: user.blocked || []
        }
    });
}

function handleLogout(req, res) {
    const token = getToken(req);
    destroySession(token);
    sendJSON(res, 200, { ok: true });
}

/* ========== HEARTBEAT / STATUS ========== */

async function handleHeartbeat(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const users = readUsers();
        const user = users.find(u => u.username.toLowerCase() === me.username.toLowerCase());
        if (user) {
            user.lastSeen = new Date().toISOString();
            saveUsers(users);
            const dms = readDms();
            let changed = false;
            dms.forEach(m => { if (m.to && m.to.toLowerCase() === me.username.toLowerCase() && !m.delivered) { m.delivered = true; changed = true; } });
            if (changed) saveDms(dms);
        }
        sendJSON(res, 200, { ok: true });
    } catch (e) { sendJSON(res, 500, { error: 'Error' }); }
}
function handleUserStatus(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const target = (query.username || '').trim().toLowerCase();
    const u = readUsers().find(x => x.username.toLowerCase() === target);
    if (!u) return sendJSON(res, 404, { error: 'User not found' });
    sendJSON(res, 200, { lastSeen: u.lastSeen || u.createdAt });
}

/* ========== CALLS ========== */

async function handleCallSignalSend(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const { to, type, sdp, candidate } = data;
        const from = me.username;
        if (!to || !type) return sendJSON(res, 400, { error: 'Missing call params' });
        if (typeof to !== 'string' || !CALL_TYPES.includes(type)) return sendJSON(res, 400, { error: 'Некорректный сигнал' });
        if (sdp !== undefined && (typeof sdp !== 'string' || sdp.length > 30000)) return sendJSON(res, 400, { error: 'Некорректный сигнал' });
        if (candidate !== undefined && JSON.stringify(candidate).length > 3000) return sendJSON(res, 400, { error: 'Некорректный сигнал' });
        const retry = rateLimit(req, 'callsig', 800, me.username);
        if (retry) return sendJSON(res, 429, { error: 'Слишком много запросов', retryAfter: retry });
        const users = readUsers();
        const fromU = users.find(u => u.username.toLowerCase() === String(from).toLowerCase());
        const toU = users.find(u => u.username.toLowerCase() === String(to).toLowerCase());
        if (!fromU || !toU) return sendJSON(res, 404, { error: 'Пользователь не найден' });
        if ((fromU.blocked || []).some(b => b.toLowerCase() === toU.username.toLowerCase())) return sendJSON(res, 403, { error: 'Вы заблокировали этого пользователя' });
        if ((toU.blocked || []).some(b => b.toLowerCase() === fromU.username.toLowerCase())) return sendJSON(res, 403, { error: 'Пользователь заблокировал вас' });
        pushCallSignal(toU.username, { from, to: toU.username, type, sdp, candidate, time: Date.now() });
        sendJSON(res, 200, { ok: true });
    } catch (e) { sendJSON(res, 500, { error: 'Error' }); }
}
function handleCallSignalPoll(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    sendJSON(res, 200, { signals: popCallSignals(me.username) });
}

async function handleCallLog(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const from = me.username;
        const to = (data.to || '').trim();
        const type = (data.type || '').trim();
        const duration = parseInt(data.duration || 0, 10) || 0;
        if (!to || !type) return sendJSON(res, 400, { error: 'Недостаточно данных' });
        if (!['outgoing', 'incoming', 'missed', 'cancelled', 'declined'].includes(type)) return sendJSON(res, 400, { error: 'Неизвестный тип звонка' });
        const allUsers = readUsers();
        const fromU = allUsers.find(u => u.username.toLowerCase() === from.toLowerCase());
        const toU = allUsers.find(u => u.username.toLowerCase() === to.toLowerCase());
        if (!fromU || !toU) return sendJSON(res, 404, { error: 'Пользователь не найден' });
        if ((fromU.blocked || []).some(b => b.toLowerCase() === toU.username.toLowerCase()) || (toU.blocked || []).some(b => b.toLowerCase() === fromU.username.toLowerCase())) return sendJSON(res, 403, { error: 'Звонок невозможен: блокировка' });
        const msg = { id: makeId(), from, to: toU.username, type: 'call', callType: type, duration: Math.min(Math.max(duration, 0), 86400), delivered: true, read: true, createdAt: new Date().toISOString() };
        const dms = readDms();
        dms.push(msg);
        saveDms(dms.length > 5000 ? dms.slice(-5000) : dms);
        sendJSON(res, 201, { message: msg });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}

/* ========== BLOCK ========== */

async function handleBlockToggle(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const target = (data.target || '').trim();
        if (!target) return sendJSON(res, 400, { error: 'Недостаточно данных' });
        if (me.username.toLowerCase() === target.toLowerCase()) return sendJSON(res, 400, { error: 'Нельзя заблокировать себя' });
        const users = readUsers();
        const meUser = users.find(u => u.username.toLowerCase() === me.username.toLowerCase());
        const targetUser = users.find(u => u.username.toLowerCase() === target.toLowerCase());
        if (!meUser || !targetUser) return sendJSON(res, 404, { error: 'Пользователь не найден' });
        if (!Array.isArray(meUser.blocked)) meUser.blocked = [];
        const lowerTarget = targetUser.username.toLowerCase();
        const idx = meUser.blocked.findIndex(b => b.toLowerCase() === lowerTarget);
        let blocked;
        if (idx === -1) { meUser.blocked.push(targetUser.username); blocked = true; }
        else { meUser.blocked.splice(idx, 1); blocked = false; }
        saveUsers(users);
        sendJSON(res, 200, { blocked, blockedList: meUser.blocked });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
function handleBlockedList(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const users = readUsers();
    const meUser = users.find(u => u.username.toLowerCase() === me.username.toLowerCase());
    if (!meUser) return sendJSON(res, 404, { error: 'Пользователь не найден' });
    const blockedNames = Array.isArray(meUser.blocked) ? meUser.blocked : [];
    const list = users
        .filter(u => blockedNames.some(b => b.toLowerCase() === u.username.toLowerCase()))
        .map(u => ({ username: u.username, avatar: u.avatar || '', handle: u.handle || '' }));
    sendJSON(res, 200, { blocked: list });
}
function handleBlockStatus(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const target = (query.target || '').trim().toLowerCase();
    const users = readUsers();
    const meUser = users.find(u => u.username.toLowerCase() === me.username.toLowerCase());
    const targetUser = users.find(u => u.username.toLowerCase() === target);
    if (!meUser || !targetUser) return sendJSON(res, 404, { error: 'Пользователь не найден' });
    const iBlocked = (meUser.blocked || []).some(b => b.toLowerCase() === target);
    const heBlocked = (targetUser.blocked || []).some(b => b.toLowerCase() === me.username.toLowerCase());
    sendJSON(res, 200, { iBlocked, heBlocked, mutual: iBlocked || heBlocked });
}

/* ========== FORWARD ========== */

async function handleForward(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const cdWait = msgCooldown(me.username); if (cdWait > 0) return cooldownReply(res, cdWait);
        const to = (data.to || '').trim();
        const text = (data.text || '').trim();
        const originalFrom = (data.originalFrom || '').trim();
        if (!to || !text) return sendJSON(res, 400, { error: 'Недостаточно данных' });
        const users = readUsers();
        const sender = users.find(u => u.username.toLowerCase() === me.username.toLowerCase());
        const recipient = users.find(u => u.username.toLowerCase() === to.toLowerCase());
        if (!sender || !recipient) return sendJSON(res, 404, { error: 'Пользователь не найден' });
        if ((sender.blocked || []).some(b => b.toLowerCase() === to.toLowerCase())) return sendJSON(res, 403, { error: 'Вы заблокировали этого пользователя' });
        if ((recipient.blocked || []).some(b => b.toLowerCase() === me.username.toLowerCase())) return sendJSON(res, 403, { error: 'Пользователь заблокировал вас' });
        const isOnline = recipient.lastSeen && (Date.now() - new Date(recipient.lastSeen).getTime() < 35000);
        const message = {
            id: makeId(), from: sender.username, to: recipient.username, text,
            forwardedFrom: originalFrom || null,
            delivered: !!isOnline, read: false, createdAt: new Date().toISOString()
        };
        const dms = readDms();
        dms.push(message);
        saveDms(dms.length > 5000 ? dms.slice(-5000) : dms);
        sendJSON(res, 201, { message });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}

/* ========== PROFILE ========== */

async function handleUpdateProfile(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req, MAX_BODY_SIZE);
        const newUsername = (data.newUsername || '').trim();
        const hasAvatar = Object.prototype.hasOwnProperty.call(data, 'avatar');
        const avatar = data.avatar;
        const hasHandle = Object.prototype.hasOwnProperty.call(data, 'handle');
        const handle = hasHandle ? normalizeHandle(typeof data.handle === 'string' ? data.handle : '') : null;
        const hasTheme = Object.prototype.hasOwnProperty.call(data, 'theme');
        const theme = hasTheme && (data.theme === 'light' || data.theme === 'dark') ? data.theme : null;
        const hasWallpaper = Object.prototype.hasOwnProperty.call(data, 'wallpaper');
        const wallpaper = hasWallpaper && typeof data.wallpaper === 'string' ? data.wallpaper : null;
        const hasBirthday = Object.prototype.hasOwnProperty.call(data, 'birthday');
        const birthdayRaw = hasBirthday && typeof data.birthday === 'string' ? data.birthday.trim() : '';
        if (hasBirthday && birthdayRaw && !/^\d{4}-\d{2}-\d{2}$/.test(birthdayRaw)) return sendJSON(res, 400, { error: 'Некорректная дата рождения' });
        if (hasBirthday && birthdayRaw) {
            const [y, m, d] = birthdayRaw.split('-').map(Number);
            const dt = new Date(Date.UTC(y, m - 1, d));
            if (dt.getUTCFullYear() !== y || dt.getUTCMonth() !== m - 1 || dt.getUTCDate() !== d) return sendJSON(res, 400, { error: 'Некорректная дата рождения' });
            if (dt.getTime() > Date.now()) return sendJSON(res, 400, { error: 'Некорректная дата рождения' });
        }
        if (!HANDLE_RE.test(newUsername)) return sendJSON(res, 400, { error: 'Ник: 3-20 символов, только латиница, цифры и _' });
        if (hasAvatar && typeof avatar === 'string' && avatar.length > MAX_BODY_SIZE) return sendJSON(res, 400, { error: 'Аватар слишком большой' });
        if (hasHandle && handle && !HANDLE_RE.test(handle)) return sendJSON(res, 400, { error: 'Юзернейм: 3-20 символов, латиница, цифры и _' });
        const processedAvatar = hasAvatar ? processImageInput(avatar, true) : null;
        if (hasAvatar && processedAvatar === null) return sendJSON(res, 400, { error: 'Аватар: разрешены PNG, JPG, WEBP или GIF до 5 МБ' });
        const processedWallpaper = hasWallpaper ? processImageInput(wallpaper, true) : null;
        if (hasWallpaper && processedWallpaper === null) return sendJSON(res, 400, { error: 'Обои: разрешены PNG, JPG, WEBP или GIF до 5 МБ' });
        const users = readUsers();
        const user = users.find(u => u.username.toLowerCase() === me.username.toLowerCase());
        if (!user) return sendJSON(res, 404, { error: 'Пользователь не найден' });
        const lowerNewName = newUsername.toLowerCase();
        const lowerOldName = user.username.toLowerCase();
        const usernameChanged = lowerNewName !== lowerOldName;
        const avatarChanged = hasAvatar && processedAvatar !== user.avatar;
        if (usernameChanged && users.some(u => u !== user && u.username.toLowerCase() === lowerNewName)) return sendJSON(res, 409, { error: 'Такое имя уже занято' });
        if (hasHandle && handle && users.some(u => u !== user && (u.handle || '').toLowerCase() === handle.toLowerCase())) return sendJSON(res, 409, { error: 'Такой юзернейм уже занят' });
        user.username = newUsername;
        if (hasAvatar) user.avatar = processedAvatar;
        if (hasHandle) user.handle = handle;
        if (hasTheme && theme) user.theme = theme;
        if (hasWallpaper) user.wallpaper = processedWallpaper;
        if (hasBirthday) user.birthday = birthdayRaw;
        if (usernameChanged) {
            users.forEach(u => {
                if (Array.isArray(u.friends)) u.friends = u.friends.map(f => f.toLowerCase() === lowerOldName ? newUsername : f);
                if (Array.isArray(u.incomingRequests)) u.incomingRequests = u.incomingRequests.map(r => r.toLowerCase() === lowerOldName ? newUsername : r);
                if (Array.isArray(u.blocked)) u.blocked = u.blocked.map(b => b.toLowerCase() === lowerOldName ? newUsername : b);
            });
        }
        saveUsers(users);
        if (usernameChanged) {
            const sessions = readSessions();
            let sc = false;
            sessions.forEach(s => { if (s.username.toLowerCase() === lowerOldName) { s.username = newUsername; sc = true; } });
            if (sc) saveSessions(sessions);
        }
        if (usernameChanged || avatarChanged) {
            if (usernameChanged) {
                const dms = readDms();
                let changed = false;
                dms.forEach(m => {
                    if (m.from && m.from.toLowerCase() === lowerOldName) { m.from = newUsername; changed = true; }
                    if (m.to && m.to.toLowerCase() === lowerOldName) { m.to = newUsername; changed = true; }
                });
                if (changed) saveDms(dms);
            }
            const posts = readPosts();
            let pc = false;
            posts.forEach(p => {
                if (p.username.toLowerCase() === lowerOldName) { p.username = newUsername; if (avatarChanged) p.avatar = user.avatar; pc = true; }
                if (p.repostOf && p.repostOf.username && p.repostOf.username.toLowerCase() === lowerOldName) { p.repostOf.username = newUsername; if (avatarChanged) p.repostOf.avatar = user.avatar; pc = true; }
                if (Array.isArray(p.likes)) { const i = p.likes.findIndex(l => l.toLowerCase() === lowerOldName); if (i !== -1) { p.likes[i] = newUsername; pc = true; } }
                if (Array.isArray(p.comments)) p.comments.forEach(c => { if (c.username.toLowerCase() === lowerOldName) { c.username = newUsername; if (avatarChanged) c.avatar = user.avatar; pc = true; } });
            });
            if (pc) savePosts(posts);
            const channels = readChannels();
            let cc = false;
            channels.forEach(ch => {
                if (ch.owner.toLowerCase() === lowerOldName) { ch.owner = newUsername; cc = true; }
                if (Array.isArray(ch.members)) { const i = ch.members.findIndex(m => m.toLowerCase() === lowerOldName); if (i !== -1) { ch.members[i] = newUsername; cc = true; } }
            });
            if (cc) saveChannels(channels);
            const chats = readChats();
            let chc = false;
            chats.forEach(ch => {
                if (ch.owner.toLowerCase() === lowerOldName) { ch.owner = newUsername; chc = true; }
                if (Array.isArray(ch.members)) { const i = ch.members.findIndex(m => m.toLowerCase() === lowerOldName); if (i !== -1) { ch.members[i] = newUsername; chc = true; } }
                if (Array.isArray(ch.messages)) ch.messages.forEach(msg => {
                    if (msg.from && msg.from.toLowerCase() === lowerOldName) { msg.from = newUsername; chc = true; }
                    if (Array.isArray(msg.read)) msg.read = msg.read.map(r => r.toLowerCase() === lowerOldName ? newUsername : r);
                });
            });
            if (chc) saveChats(chats);
        }
        sendJSON(res, 200, {
            user: {
                username: user.username, email: user.email, avatar: user.avatar || '',
                handle: user.handle || '', theme: user.theme || 'dark',
                wallpaper: user.wallpaper || '', birthday: user.birthday || '',
                friends: user.friends || [], blocked: user.blocked || []
            }
        });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}

/* ========== FRIENDS ========== */

async function handleFriendAction(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const target = (data.target || '').trim();
        const action = (data.action || '').trim();
        if (!target || !action) return sendJSON(res, 400, { error: 'Недостаточно данных' });
        if (me.username.toLowerCase() === target.toLowerCase()) return sendJSON(res, 400, { error: 'Нельзя выполнить действие с собой' });
        const users = readUsers();
        const meUser = users.find(u => u.username.toLowerCase() === me.username.toLowerCase());
        const targetUser = users.find(u => u.username.toLowerCase() === target.toLowerCase());
        if (!meUser || !targetUser) return sendJSON(res, 404, { error: 'Пользователь не найден' });
        if (!Array.isArray(meUser.friends)) meUser.friends = [];
        if (!Array.isArray(targetUser.friends)) targetUser.friends = [];
        if (!Array.isArray(meUser.incomingRequests)) meUser.incomingRequests = [];
        if (!Array.isArray(targetUser.incomingRequests)) targetUser.incomingRequests = [];
        const lowerMe = meUser.username.toLowerCase();
        const lowerTarget = targetUser.username.toLowerCase();
        if (action === 'send') {
            if ((meUser.blocked || []).some(b => b.toLowerCase() === lowerTarget)) return sendJSON(res, 403, { error: 'Вы заблокировали этого пользователя' });
            if ((targetUser.blocked || []).some(b => b.toLowerCase() === lowerMe)) return sendJSON(res, 403, { error: 'Пользователь заблокировал вас' });
            if (!targetUser.incomingRequests.some(r => r.toLowerCase() === lowerMe)) targetUser.incomingRequests.push(meUser.username);
        } else if (action === 'cancel') {
            targetUser.incomingRequests = targetUser.incomingRequests.filter(r => r.toLowerCase() !== lowerMe);
        } else if (action === 'accept') {
            meUser.incomingRequests = meUser.incomingRequests.filter(r => r.toLowerCase() !== lowerTarget);
            if (!meUser.friends.some(f => f.toLowerCase() === lowerTarget)) meUser.friends.push(targetUser.username);
            if (!targetUser.friends.some(f => f.toLowerCase() === lowerMe)) targetUser.friends.push(meUser.username);
        } else if (action === 'decline') {
            meUser.incomingRequests = meUser.incomingRequests.filter(r => r.toLowerCase() !== lowerTarget);
        } else if (action === 'remove') {
            meUser.friends = meUser.friends.filter(f => f.toLowerCase() !== lowerTarget);
            targetUser.friends = targetUser.friends.filter(f => f.toLowerCase() !== lowerMe);
        }
        saveUsers(users);
        sendJSON(res, 200, { ok: true, meFriends: meUser.friends, incomingCount: meUser.incomingRequests.length });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
function handleFriendStatus(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const target = (query.target || '').trim().toLowerCase();
    const users = readUsers();
    const meUser = users.find(u => u.username.toLowerCase() === me.username.toLowerCase());
    const targetUser = users.find(u => u.username.toLowerCase() === target);
    if (!meUser || !targetUser) return sendJSON(res, 404, { error: 'Пользователь не найден' });
    const isFriends = (meUser.friends || []).some(f => f.toLowerCase() === target);
    const isSent = (targetUser.incomingRequests || []).some(r => r.toLowerCase() === me.username.toLowerCase());
    const isReceived = (meUser.incomingRequests || []).some(r => r.toLowerCase() === target);
    let status = 'none';
    if (isFriends) status = 'friends';
    else if (isReceived) status = 'received';
    else if (isSent) status = 'sent';
    sendJSON(res, 200, { status });
}
function handleFriendsGet(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const users = readUsers();
    const user = users.find(u => u.username.toLowerCase() === me.username.toLowerCase());
    if (!user) return sendJSON(res, 404, { error: 'Пользователь не найден' });
    const friendNames = Array.isArray(user.friends) ? user.friends : [];
    const friends = users.filter(u => friendNames.some(fn => fn.toLowerCase() === u.username.toLowerCase())).map(u => ({ username: u.username, avatar: u.avatar || '', handle: u.handle || '', birthday: u.birthday || '' }));
    const reqNames = Array.isArray(user.incomingRequests) ? user.incomingRequests : [];
    const requests = users.filter(u => reqNames.some(rn => rn.toLowerCase() === u.username.toLowerCase())).map(u => ({ username: u.username, avatar: u.avatar || '', handle: u.handle || '' }));
    sendJSON(res, 200, { friends, requests });
}

/* ========== USERS ========== */

function handleUsersList(req, res) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const safe = readUsers().map(u => ({ username: u.username, avatar: u.avatar || '', handle: u.handle || '', theme: u.theme || 'dark', friends: u.friends || [], lastSeen: u.lastSeen || u.createdAt, createdAt: u.createdAt }));
    sendJSON(res, 200, { users: safe });
}
function handleUserSearch(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const q = normalizeHandle(query.q || '').toLowerCase();
    const users = readUsers();
    const results = q ? users.filter(u => (u.handle || '').toLowerCase().includes(q) || u.username.toLowerCase().includes(q)) : users;
    sendJSON(res, 200, { users: results.slice(0, 20).map(u => ({ username: u.username, avatar: u.avatar || '', handle: u.handle || '' })) });
}

/* ========== POSTS ========== */

function normalizePost(p, repostedByViewer) {
    return { id: p.id, username: p.username, avatar: p.avatar || '', text: p.text || '', image: p.image || '', createdAt: p.createdAt, likes: Array.isArray(p.likes) ? p.likes : [], comments: Array.isArray(p.comments) ? p.comments : [], repostOf: p.repostOf || null, repostCount: typeof p.repostCount === 'number' ? p.repostCount : 0, repostedByViewer: !!repostedByViewer };
}
function handleFeedGet(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const viewer = me.username.toLowerCase();
    const allPosts = readPosts();
    const feedPosts = allPosts.filter(p => !p.repostOf);
    const viewerReposts = new Set();
    allPosts.forEach(p => { if (p.username && p.username.toLowerCase() === viewer && p.repostOf && p.repostOf.id) viewerReposts.add(p.repostOf.id); });
    const posts = feedPosts.map(p => normalizePost(p, viewerReposts.has(p.id)));
    posts.sort((a, b) => new Date(b.createdAt) - new Date(a.createdAt));
    sendJSON(res, 200, { posts: posts.slice(0, FEED_LIMIT) });
}
function handlePostsGet(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const username = (query.username || '').trim();
    if (!username) return sendJSON(res, 400, { error: 'Не указан пользователь' });
    const allPosts = readPosts();
    const viewer = me.username.toLowerCase();
    const viewerReposts = new Set();
    allPosts.forEach(p => { if (p.username && p.username.toLowerCase() === viewer && p.repostOf && p.repostOf.id) viewerReposts.add(p.repostOf.id); });
    const posts = allPosts.map(p => normalizePost(p, viewerReposts.has(p.id) || (p.repostOf && viewerReposts.has(p.repostOf.id))));
    const filtered = posts.filter(p => p.username.toLowerCase() === username.toLowerCase());
    filtered.sort((a, b) => new Date(b.createdAt) - new Date(a.createdAt));
    sendJSON(res, 200, { posts: filtered.slice(0, POSTS_PER_WALL) });
}
async function handlePostsCreate(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req, MAX_BODY_SIZE);
        const text = (data.text || '').trim();
        const image = processImageInput(typeof data.image === 'string' ? data.image : '', true);
        if (image === null) return sendJSON(res, 400, { error: 'Картинка: разрешены PNG, JPG, WEBP или GIF до 5 МБ' });
        if (!text && !image) return sendJSON(res, 400, { error: 'Пустой пост' });
        const author = readUsers().find(u => u.username.toLowerCase() === me.username.toLowerCase());
        if (!author) return sendJSON(res, 404, { error: 'Пользователь не найден' });
        const post = { id: makeId(), username: author.username, avatar: author.avatar || '', text, image, createdAt: new Date().toISOString(), likes: [], comments: [], repostOf: null, repostCount: 0 };
        const posts = readPosts();
        posts.push(post);
        savePosts(posts.length > 3000 ? posts.slice(-3000) : posts);
        sendJSON(res, 201, { post: normalizePost(post) });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
async function handlePostLike(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const id = (data.id || '').trim();
        const username = me.username;
        const posts = readPosts();
        const idx = posts.findIndex(p => p.id === id);
        if (idx === -1) return sendJSON(res, 404, { error: 'Пост не найден' });
        if (!Array.isArray(posts[idx].likes)) posts[idx].likes = [];
        const lower = username.toLowerCase();
        const uIdx = posts[idx].likes.findIndex(u => u.toLowerCase() === lower);
        if (uIdx === -1) posts[idx].likes.push(username); else posts[idx].likes.splice(uIdx, 1);
        savePosts(posts);
        sendJSON(res, 200, { likes: posts[idx].likes, liked: uIdx === -1 });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
async function handlePostComment(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const id = (data.id || '').trim();
        const text = (data.text || '').trim();
        const author = readUsers().find(u => u.username.toLowerCase() === me.username.toLowerCase());
        if (!author) return sendJSON(res, 404, { error: 'Пользователь не найден' });
        const posts = readPosts();
        const idx = posts.findIndex(p => p.id === id);
        if (idx === -1) return sendJSON(res, 404, { error: 'Пост не найден' });
        if (!Array.isArray(posts[idx].comments)) posts[idx].comments = [];
        const comment = { id: makeId(), username: author.username, avatar: author.avatar || '', text, createdAt: new Date().toISOString() };
        posts[idx].comments.push(comment);
        savePosts(posts);
        sendJSON(res, 201, { comment, comments: posts[idx].comments });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
function handleCommentsGet(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const post = readPosts().find(p => p.id === (query.id || '').trim());
    if (!post) return sendJSON(res, 404, { error: 'Пост не найден' });
    sendJSON(res, 200, { comments: Array.isArray(post.comments) ? post.comments : [] });
}
async function handlePostRepost(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const id = (data.id || '').trim();
        const author = readUsers().find(u => u.username.toLowerCase() === me.username.toLowerCase());
        if (!author) return sendJSON(res, 404, { error: 'Пользователь не найден' });
        const posts = readPosts();
        const target = posts.find(p => p.id === id);
        if (!target) return sendJSON(res, 404, { error: 'Пост не найден' });
        const originalId = target.repostOf && target.repostOf.id ? target.repostOf.id : target.id;
        const original = posts.find(p => p.id === originalId);
        if (!original) return sendJSON(res, 404, { error: 'Оригинал не найден' });
        let removed = 0;
        const kept = [];
        posts.forEach(p => {
            if (p.repostOf && p.repostOf.id === originalId && p.username && p.username.toLowerCase() === author.username.toLowerCase()) removed++;
            else kept.push(p);
        });
        if (removed > 0) {
            original.repostCount = Math.max(0, (original.repostCount || 0) - removed);
            savePosts(kept);
            return sendJSON(res, 200, { reposted: false, repostCount: original.repostCount });
        }
        const repost = { id: makeId(), username: author.username, avatar: author.avatar || '', text: '', image: '', createdAt: new Date().toISOString(), likes: [], comments: [], repostOf: { id: original.id, username: original.username, avatar: original.avatar || '', text: original.text || '', image: original.image || '', createdAt: original.createdAt }, repostCount: 0 };
        original.repostCount = (original.repostCount || 0) + 1;
        kept.push(repost);
        savePosts(kept);
        sendJSON(res, 201, { reposted: true, post: normalizePost(repost, true), repostCount: original.repostCount });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
async function handlePostDelete(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const postId = (data.postId || '').trim();
        if (!postId) return sendJSON(res, 400, { error: 'Недостаточно данных' });
        const posts = readPosts();
        const idx = posts.findIndex(p => p.id === postId);
        if (idx === -1) return sendJSON(res, 404, { error: 'Пост не найден' });
        if (!posts[idx].username || posts[idx].username.toLowerCase() !== me.username.toLowerCase()) return sendJSON(res, 403, { error: 'Можно удалять только свои посты' });
        const removed = posts[idx];
        if (removed.repostOf && removed.repostOf.id) {
            const origIdx = posts.findIndex(p => p.id === removed.repostOf.id);
            if (origIdx !== -1 && typeof posts[origIdx].repostCount === 'number') {
                posts[origIdx].repostCount = Math.max(0, posts[origIdx].repostCount - 1);
            }
        }
        posts.splice(idx, 1);
        savePosts(posts);
        sendJSON(res, 200, { ok: true });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
async function handleCommentDelete(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const postId = (data.postId || '').trim();
        const commentId = (data.commentId || '').trim();
        if (!postId || !commentId) return sendJSON(res, 400, { error: 'Недостаточно данных' });
        const posts = readPosts();
        const p = posts.find(x => x.id === postId);
        if (!p) return sendJSON(res, 404, { error: 'Пост не найден' });
        if (!Array.isArray(p.comments)) return sendJSON(res, 404, { error: 'Комментарий не найден' });
        const cIdx = p.comments.findIndex(c => c.id === commentId);
        if (cIdx === -1) return sendJSON(res, 404, { error: 'Комментарий не найден' });
        if (!p.comments[cIdx].username || p.comments[cIdx].username.toLowerCase() !== me.username.toLowerCase()) return sendJSON(res, 403, { error: 'Можно удалять только свои комментарии' });
        p.comments.splice(cIdx, 1);
        savePosts(posts);
        sendJSON(res, 200, { ok: true });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}

/* ========== CHANNELS ========== */

function channelPublic(c, viewer) {
    const isSub = viewer ? (c.members || []).some(m => m.toLowerCase() === viewer.toLowerCase()) : false;
    return { id: c.id, username: c.username, name: c.name, description: c.description || '', avatar: c.avatar || '', owner: c.owner, createdAt: c.createdAt, members: Array.isArray(c.members) ? c.members.length : 0, isSubscribed: isSub };
}
async function handleChannelCreate(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req, MAX_BODY_SIZE);
        const name = (data.name || '').trim();
        const username = normalizeHandle(data.username || '');
        if (!name || !username) return sendJSON(res, 400, { error: 'Заполните название и юзернейм канала' });
        if (!HANDLE_RE.test(username)) return sendJSON(res, 400, { error: 'Юзернейм: 3-20 символов' });
        const channels = readChannels();
        if (channels.some(c => c.username.toLowerCase() === username.toLowerCase())) return sendJSON(res, 409, { error: 'Юзернейм канала занят' });
        const channelAvatar = processImageInput(typeof data.avatar === 'string' ? data.avatar : '', true);
        if (channelAvatar === null) return sendJSON(res, 400, { error: 'Аватар канала: разрешены PNG, JPG, WEBP или GIF до 5 МБ' });
        const channel = { id: makeId(), username, name, description: (data.description || '').trim(), avatar: channelAvatar, owner: me.username, members: [me.username], messages: [], pinnedMessageId: null, createdAt: new Date().toISOString() };
        channels.push(channel); saveChannels(channels);
        sendJSON(res, 201, { channel: channelPublic(channel, me.username) });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
async function handleChannelUpdate(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req, MAX_BODY_SIZE);
        const originalUsername = normalizeHandle(data.originalUsername || '');
        const newName = (data.name || '').trim();
        const newUsername = normalizeHandle(data.username || '');
        const description = (data.description || '').trim();
        const avatarInput = typeof data.avatar === 'string' ? data.avatar : null;
        const avatar = avatarInput === null ? null : processImageInput(avatarInput, true);
        if (avatarInput !== null && avatar === null) return sendJSON(res, 400, { error: 'Аватар канала: разрешены PNG, JPG, WEBP или GIF до 5 МБ' });
        if (!originalUsername || !newName || !newUsername) return sendJSON(res, 400, { error: 'Заполните все поля' });
        if (!HANDLE_RE.test(newUsername)) return sendJSON(res, 400, { error: 'Юзернейм: 3-20 символов' });
        const channels = readChannels();
        const ch = channels.find(c => c.username.toLowerCase() === originalUsername.toLowerCase());
        if (!ch) return sendJSON(res, 404, { error: 'Канал не найден' });
        if (ch.owner.toLowerCase() !== me.username.toLowerCase()) return sendJSON(res, 403, { error: 'Только владелец' });
        if (newUsername.toLowerCase() !== originalUsername.toLowerCase() && channels.some(c => c.username.toLowerCase() === newUsername.toLowerCase())) return sendJSON(res, 409, { error: 'Занят' });
        ch.name = newName; ch.username = newUsername; ch.description = description;
        if (avatar !== null) ch.avatar = avatar;
        saveChannels(channels);
        sendJSON(res, 200, { channel: channelPublic(ch, me.username) });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
async function handleChannelSubscribe(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const channelUsername = normalizeHandle(data.channel || data.username || '');
        if (!channelUsername) return sendJSON(res, 400, { error: 'Не хватает данных' });
        const channels = readChannels();
        const ch = channels.find(c => c.username.toLowerCase() === channelUsername.toLowerCase());
        if (!ch) return sendJSON(res, 404, { error: 'Канал не найден' });
        if (!Array.isArray(ch.members)) ch.members = [];
        const lowerUser = me.username.toLowerCase();
        const idx = ch.members.findIndex(m => m.toLowerCase() === lowerUser);
        let subscribed;
        if (idx === -1) { ch.members.push(me.username); subscribed = true; } else { ch.members.splice(idx, 1); subscribed = false; }
        saveChannels(channels);
        sendJSON(res, 200, { subscribed, memberCount: ch.members.length });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
function handleChannelGet(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const c = readChannels().find(x => x.username.toLowerCase() === normalizeHandle(query.username || '').toLowerCase());
    if (!c) return sendJSON(res, 404, { error: 'Канал не найден' });
    sendJSON(res, 200, { channel: channelPublic(c, me.username) });
}
function handleChannelSearch(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const q = normalizeHandle(query.q || '').toLowerCase();
    const channels = readChannels();
    const found = q ? channels.filter(c => c.username.toLowerCase().includes(q) || c.name.toLowerCase().includes(q)) : channels;
    sendJSON(res, 200, { channels: found.slice(0, 20).map(c => channelPublic(c, me.username)) });
}
function handleChannelMessagesGet(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const c = readChannels().find(x => x.username.toLowerCase() === normalizeHandle(query.username || '').toLowerCase());
    if (!c) return sendJSON(res, 404, { error: 'Канал не найден' });
    sendJSON(res, 200, { messages: (c.messages || []).slice(-300), pinnedMessageId: c.pinnedMessageId || null });
}
async function handleChannelMessageCreate(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req, MAX_BODY_SIZE);
        const cdWait = msgCooldown(me.username); if (cdWait > 0) return cooldownReply(res, cdWait);
        const channels = readChannels();
        const c = channels.find(x => x.username.toLowerCase() === normalizeHandle(data.channel || '').toLowerCase());
        if (!c) return sendJSON(res, 404, { error: 'Канал не найден' });
        if (c.owner.toLowerCase() !== me.username.toLowerCase()) return sendJSON(res, 403, { error: 'Только владелец' });
        let fileInfo = null;
        if (data.file && typeof data.file === 'object' && typeof data.file.data === 'string') {
            { const upRetry = rateLimit(req, 'upload', 30, me.username); if (upRetry) return sendJSON(res, 429, { error: 'Слишком много загрузок, подожди ' + upRetry + ' с' }); }
            const fname = String(data.file.name || 'file').replace(/[\\/\r\n<>"]/g, '_').slice(0, 120);
            const a = saveAttachment(data.file.data, 'file', fname);
            if (!a) return sendJSON(res, 400, { error: 'Файл слишком большой или имеет недопустимый формат (до 20 МБ)' });
            fileInfo = { name: fname, size: a.size, url: a.url };
        }
        const text = (data.text || '').trim();
        if (!text && !fileInfo) return sendJSON(res, 400, { error: 'Пустое сообщение' });
        const msg = { id: makeId(), from: c.name, channelUsername: c.username, channelAvatar: c.avatar || '', text, file: fileInfo, reactions: { like: [], fire: [], demon: [] }, createdAt: new Date().toISOString() };
        if (!Array.isArray(c.messages)) c.messages = [];
        c.messages.push(msg);
        if (c.messages.length > 300) c.messages = c.messages.slice(-300);
        saveChannels(channels);
        sendJSON(res, 201, { message: msg });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
async function handleChannelMessageReaction(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const channelUsername = normalizeHandle(data.channel || '');
        const messageId = (data.messageId || '').trim();
        const reactionType = (data.type || '').trim();
        if (!['like', 'fire', 'demon'].includes(reactionType)) return sendJSON(res, 400, { error: 'Неизвестный тип реакции' });
        const channels = readChannels();
        const c = channels.find(x => x.username.toLowerCase() === channelUsername.toLowerCase());
        if (!c) return sendJSON(res, 404, { error: 'Канал не найден' });
        const msg = (c.messages || []).find(m => m.id === messageId);
        if (!msg) return sendJSON(res, 404, { error: 'Сообщение не найдено' });
        if (!msg.reactions) msg.reactions = { like: [], fire: [], demon: [] };
        if (!Array.isArray(msg.reactions[reactionType])) msg.reactions[reactionType] = [];
        const lowerUser = me.username.toLowerCase();
        const idx = msg.reactions[reactionType].findIndex(u => u.toLowerCase() === lowerUser);
        if (idx === -1) msg.reactions[reactionType].push(me.username);
        else msg.reactions[reactionType].splice(idx, 1);
        saveChannels(channels);
        sendJSON(res, 200, { reactions: msg.reactions });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
async function handleChannelPin(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const channelUsername = normalizeHandle(data.channel || '');
        const messageId = (data.messageId || '').trim();
        const pinned = !!data.pinned;
        if (!channelUsername) return sendJSON(res, 400, { error: 'Недостаточно данных' });
        const channels = readChannels();
        const c = channels.find(x => x.username.toLowerCase() === channelUsername.toLowerCase());
        if (!c) return sendJSON(res, 404, { error: 'Канал не найден' });
        if (c.owner.toLowerCase() !== me.username.toLowerCase()) return sendJSON(res, 403, { error: 'Только владелец канала может закреплять' });
        if (pinned) {
            if (!messageId) return sendJSON(res, 400, { error: 'Не указано сообщение' });
            const msg = (c.messages || []).find(m => m.id === messageId);
            if (!msg) return sendJSON(res, 404, { error: 'Сообщение не найдено' });
            c.pinnedMessageId = messageId;
        } else {
            c.pinnedMessageId = null;
        }
        saveChannels(channels);
        sendJSON(res, 200, { ok: true, pinnedMessageId: c.pinnedMessageId });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
async function handleChannelMessageDelete(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const channelUsername = normalizeHandle(data.channel || '');
        const messageId = (data.messageId || '').trim();
        if (!channelUsername || !messageId) return sendJSON(res, 400, { error: 'Недостаточно данных' });
        const channels = readChannels();
        const c = channels.find(x => x.username.toLowerCase() === channelUsername.toLowerCase());
        if (!c) return sendJSON(res, 404, { error: 'Канал не найден' });
        if (c.owner.toLowerCase() !== me.username.toLowerCase()) return sendJSON(res, 403, { error: 'Только владелец канала может удалять сообщения' });
        const before = (c.messages || []).length;
        c.messages = (c.messages || []).filter(m => m.id !== messageId);
        if (c.messages.length === before) return sendJSON(res, 404, { error: 'Сообщение не найдено' });
        if (c.pinnedMessageId === messageId) c.pinnedMessageId = null;
        saveChannels(channels);
        sendJSON(res, 200, { ok: true });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}

/* ========== CHATS ========== */

async function handleChatCreate(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const name = (data.name || '').trim();
        if (!name || name.length > 80) return sendJSON(res, 400, { error: 'Название чата: 1-80 символов' });
        const allUsers = readUsers();
        let members = Array.isArray(data.members) ? data.members.map(x => String(x).trim()).filter(Boolean) : [];
        members = members.map(function (name) { const u = allUsers.find(x => x.username.toLowerCase() === name.toLowerCase()); return u ? u.username : null; }).filter(Boolean);
        if (!members.some(x => x.toLowerCase() === me.username.toLowerCase())) members.unshift(me.username);
        members = Array.from(new Map(members.map(x => [x.toLowerCase(), x])).values()).slice(0, 100);
        const chat = { id: makeId(), name, owner: me.username, members, messages: [], pinnedMessageId: null, createdAt: new Date().toISOString() };
        const chats = readChats();
        chats.push(chat);
        saveChats(chats);
        sendJSON(res, 201, { chat: { id: chat.id, name: chat.name, owner: chat.owner, members: chat.members, memberCount: chat.members.length } });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
function handleChatsGet(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const user = me.username.toLowerCase();
    const list = readChats().filter(c => (c.members || []).some(m => m.toLowerCase() === user)).map(c => {
        const last = c.messages && c.messages.length ? c.messages[c.messages.length - 1] : null;
        let unread = 0;
        (c.messages || []).forEach(m => {
            if (m.from.toLowerCase() === user) return;
            if (!Array.isArray(m.read)) return;
            if (!m.read.some(u => u.toLowerCase() === user)) unread++;
        });
        return { id: c.id, name: c.name, owner: c.owner, members: c.members, memberCount: c.members.length, lastText: last ? last.text : '', lastAt: last ? last.createdAt : c.createdAt, unread };
    });
    sendJSON(res, 200, { chats: list });
}
function handleChatMessagesGet(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const chatId = (query.id || '').trim();
    const chats = readChats();
    const chat = chats.find(x => x.id === chatId);
    if (!chat) return sendJSON(res, 404, { error: 'Чат не найден' });
    if (!(chat.members || []).some(m => m.toLowerCase() === me.username.toLowerCase())) return sendJSON(res, 403, { error: 'Нет доступа к этому чату' });
    let changed = false;
    (chat.messages || []).forEach(m => {
        if (!Array.isArray(m.read)) m.read = [];
        if (m.from.toLowerCase() !== me.username.toLowerCase() && !m.read.some(u => u.toLowerCase() === me.username.toLowerCase())) {
            m.read.push(me.username);
            changed = true;
        }
    });
    if (changed) saveChats(chats);
    sendJSON(res, 200, {
        chat: { id: chat.id, name: chat.name, memberCount: chat.members.length, owner: chat.owner, pinnedMessageId: chat.pinnedMessageId || null },
        messages: (chat.messages || []).slice(-300)
    });
}
async function handleChatMessageCreate(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req, MAX_BODY_SIZE);
        const cdWait = msgCooldown(me.username); if (cdWait > 0) return cooldownReply(res, cdWait);
        const chats = readChats();
        const c = chats.find(x => x.id === data.id);
        if (!c) return sendJSON(res, 404, { error: 'Чат не найден' });
        if (!(c.members || []).some(m => m.toLowerCase() === me.username.toLowerCase())) return sendJSON(res, 403, { error: 'Нет доступа к этому чату' });
        const text = (data.text || '').trim();
        if (text.length > 5000) return sendJSON(res, 400, { error: 'Сообщение: максимум 5000 символов' });
        let fileInfo = null;
        if (data.file && typeof data.file === 'object' && typeof data.file.data === 'string') {
            { const upRetry = rateLimit(req, 'upload', 30, me.username); if (upRetry) return sendJSON(res, 429, { error: 'Слишком много загрузок, подожди ' + upRetry + ' с' }); }
            const fname = String(data.file.name || 'file').replace(/[\\/\r\n<>"]/g, '_').slice(0, 120);
            const a = saveAttachment(data.file.data, 'file', fname);
            if (!a) return sendJSON(res, 400, { error: 'Файл слишком большой или имеет недопустимый формат (до 20 МБ)' });
            fileInfo = { name: fname, size: a.size, url: a.url };
        }
        if (!text && !fileInfo) return sendJSON(res, 400, { error: 'Пустое сообщение' });
        const msg = { id: makeId(), from: me.username, text, file: fileInfo, read: [], createdAt: new Date().toISOString() };
        if (!Array.isArray(c.messages)) c.messages = [];
        c.messages.push(msg);
        if (c.messages.length > 300) c.messages = c.messages.slice(-300);
        saveChats(chats);
        sendJSON(res, 201, { message: msg });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
async function handleChatPin(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const chatId = (data.chatId || '').trim();
        const messageId = (data.messageId || '').trim();
        const pinned = !!data.pinned;
        if (!chatId) return sendJSON(res, 400, { error: 'Недостаточно данных' });
        const chats = readChats();
        const c = chats.find(x => x.id === chatId);
        if (!c) return sendJSON(res, 404, { error: 'Чат не найден' });
        if (c.owner.toLowerCase() !== me.username.toLowerCase()) return sendJSON(res, 403, { error: 'Только создатель чата может закреплять' });
        if (pinned) {
            if (!messageId) return sendJSON(res, 400, { error: 'Не указано сообщение' });
            const msg = (c.messages || []).find(m => m.id === messageId);
            if (!msg) return sendJSON(res, 404, { error: 'Сообщение не найдено' });
            c.pinnedMessageId = messageId;
        } else {
            c.pinnedMessageId = null;
        }
        saveChats(chats);
        sendJSON(res, 200, { ok: true, pinnedMessageId: c.pinnedMessageId });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
async function handleChatMessageDelete(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const chatId = (data.chatId || '').trim();
        const messageId = (data.messageId || '').trim();
        if (!chatId || !messageId) return sendJSON(res, 400, { error: 'Недостаточно данных' });
        const chats = readChats();
        const c = chats.find(x => x.id === chatId);
        if (!c) return sendJSON(res, 404, { error: 'Чат не найден' });
        const msg = (c.messages || []).find(m => m.id === messageId);
        if (!msg) return sendJSON(res, 404, { error: 'Сообщение не найдено' });
        const isAuthor = msg.from && msg.from.toLowerCase() === me.username.toLowerCase();
        const isOwner = c.owner && c.owner.toLowerCase() === me.username.toLowerCase();
        if (!isAuthor && !isOwner) return sendJSON(res, 403, { error: 'Можно удалять только свои сообщения' });
        c.messages = (c.messages || []).filter(m => m.id !== messageId);
        if (c.pinnedMessageId === messageId) c.pinnedMessageId = null;
        saveChats(chats);
        sendJSON(res, 200, { ok: true });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}

/* ========== DM ========== */

function handleDmGet(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const user = me.username;
    const withUser = (query.with || '').trim();
    const key = dmKey(user, withUser);
    const dms = readDms();
    let changed = false;
    dms.forEach(m => {
        if (dmKey(m.from, m.to) === key && m.to.toLowerCase() === user.toLowerCase() && m.type !== 'call') {
            if (!m.delivered) { m.delivered = true; changed = true; }
            if (!m.read) { m.read = true; changed = true; }
        }
    });
    if (changed) saveDms(dms);
    const conv = dms.filter(m => dmKey(m.from, m.to) === key);
    sendJSON(res, 200, { messages: conv.slice(-DM_HISTORY_LIMIT) });
}
async function handleDmCreate(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req, MAX_BODY_SIZE);
        const cdWait = msgCooldown(me.username); if (cdWait > 0) return cooldownReply(res, cdWait);
        const toLower = (data.to || '').trim().toLowerCase();
        const users = readUsers();
        const sender = users.find(u => u.username.toLowerCase() === me.username.toLowerCase());
        const recipient = users.find(u => u.username.toLowerCase() === toLower);
        if (!sender || !recipient) return sendJSON(res, 404, { error: 'Пользователь не найден' });
        if ((sender.blocked || []).some(b => b.toLowerCase() === toLower)) return sendJSON(res, 403, { error: 'Вы заблокировали этого пользователя' });
        if ((recipient.blocked || []).some(b => b.toLowerCase() === me.username.toLowerCase())) return sendJSON(res, 403, { error: 'Пользователь заблокировал вас' });
        const isOnline = recipient.lastSeen && (Date.now() - new Date(recipient.lastSeen).getTime() < 35000);
        let videoUrl = '', fileInfo = null;
        if (typeof data.video === 'string' && data.video) {
            { const upRetry = rateLimit(req, 'upload', 30, me.username); if (upRetry) return sendJSON(res, 429, { error: 'Слишком много загрузок, подожди ' + upRetry + ' с' }); }
            const a = saveAttachment(data.video, 'video', '');
            if (!a) return sendJSON(res, 400, { error: 'Видео не принято (форматы mp4, webm, mov, до 20 МБ)' });
            videoUrl = a.url;
        }
        if (data.file && typeof data.file === 'object' && typeof data.file.data === 'string') {
            { const upRetry = rateLimit(req, 'upload', 30, me.username); if (upRetry) return sendJSON(res, 429, { error: 'Слишком много загрузок, подожди ' + upRetry + ' с' }); }
            const fname = String(data.file.name || 'file').replace(/[\\/\r\n<>"]/g, '_').slice(0, 120);
            const a = saveAttachment(data.file.data, 'file', fname);
            if (!a) return sendJSON(res, 400, { error: 'Файл слишком большой (до 20 МБ)' });
            fileInfo = { name: fname, size: a.size, url: a.url };
        }
        const imageUrl = processImageInput(typeof data.image === 'string' ? data.image : '', true);
        if (imageUrl === null) return sendJSON(res, 400, { error: 'Картинка: разрешены PNG, JPG, WEBP или GIF до 5 МБ' });
        if (!(data.text || '').trim() && !imageUrl && !videoUrl && !fileInfo) return sendJSON(res, 400, { error: 'Пустое сообщение' });
        const message = { id: makeId(), from: sender.username, to: recipient.username, text: (data.text || '').trim(), image: imageUrl, video: videoUrl, file: fileInfo, delivered: !!isOnline, read: false, createdAt: new Date().toISOString() };
        const dms = readDms();
        dms.push(message);
        saveDms(dms.length > 5000 ? dms.slice(-5000) : dms);
        sendJSON(res, 201, { message });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}
function handleDmConversations(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const user = me.username.toLowerCase();
    const dms = readDms();
    const users = readUsers();
    const map = {};
    dms.forEach(m => {
        const fromLower = (m.from || '').toLowerCase();
        const toLower = (m.to || '').toLowerCase();
        if (fromLower !== user && toLower !== user) return;
        const partnerName = fromLower === user ? m.to : m.from;
        const partnerLower = partnerName.toLowerCase();
        if (!map[partnerLower]) map[partnerLower] = { partnerUsername: partnerName, lastMessage: m, unread: 0 };
        if (new Date(m.createdAt) > new Date(map[partnerLower].lastMessage.createdAt)) map[partnerLower].lastMessage = m;
        if (toLower === user && !m.read && m.type !== 'call') map[partnerLower].unread++;
    });
    const callLabels = { outgoing: 'Исходящий', incoming: 'Входящий', missed: 'Пропущенный', cancelled: 'Отменён', declined: 'Отклонён' };
    const list = Object.keys(map).map(k => {
        const partner = users.find(u => u.username.toLowerCase() === k);
        const lastMsg = map[k].lastMessage;
        let previewText = lastMsg.text || '';
        if (lastMsg.forwardedFrom) previewText = '↪ ' + previewText;
        if (lastMsg.type === 'call') {
            let label = callLabels[lastMsg.callType] || 'Звонок';
            let durStr = '';
            if (lastMsg.duration > 0) {
                const mm = Math.floor(lastMsg.duration / 60);
                const ss = lastMsg.duration % 60;
                durStr = ' ' + (mm < 10 ? '0' : '') + mm + ':' + (ss < 10 ? '0' : '') + ss;
            }
            previewText = label + durStr;
        }
        if (!previewText && lastMsg.image) previewText = '📷 Фото';
        if (!previewText && lastMsg.video) previewText = '🎬 Видео';
        if (!previewText && lastMsg.file) previewText = '📎 Файл';
        return { username: partner ? partner.username : map[k].partnerUsername, avatar: partner ? partner.avatar : '', handle: partner ? partner.handle : '', lastText: previewText, lastType: lastMsg.type || '', lastCallType: lastMsg.callType || '', lastFrom: lastMsg.from, lastAt: lastMsg.createdAt, unread: map[k].unread };
    }).sort((a, b) => new Date(b.lastAt) - new Date(a.lastAt));
    sendJSON(res, 200, { conversations: list });
}
function handleDmUnreadCount(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const user = me.username.toLowerCase();
    const count = readDms().filter(m => m.to && m.to.toLowerCase() === user && !m.read && m.type !== 'call').length;
    sendJSON(res, 200, { count });
}
async function handleDmDelete(req, res) {
    try {
        const me = authUser(req);
        if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
        const data = await readBody(req);
        const messageId = (data.messageId || '').trim();
        if (!messageId) return sendJSON(res, 400, { error: 'Недостаточно данных' });
        const dms = readDms();
        const idx = dms.findIndex(m => m.id === messageId);
        if (idx === -1) return sendJSON(res, 404, { error: 'Сообщение не найдено' });
        if (!dms[idx].from || dms[idx].from.toLowerCase() !== me.username.toLowerCase()) return sendJSON(res, 403, { error: 'Можно удалять только свои сообщения' });
        dms.splice(idx, 1);
        saveDms(dms);
        sendJSON(res, 200, { ok: true });
    } catch (e) { sendJSON(res, 500, { error: 'Ошибка сервера' }); }
}

/* ========== COMMUNICATION ========== */

function handleCommunication(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const user = me.username.toLowerCase();
    const channelsList = readChannels()
        .filter(c => {
            if (c.owner.toLowerCase() === user) return true;
            if ((c.members || []).some(m => m.toLowerCase() === user)) return true;
            return false;
        })
        .map(c => {
            const last = c.messages && c.messages.length ? c.messages[c.messages.length - 1] : null;
            const isOwner = c.owner.toLowerCase() === user;
            return { type: 'channel', id: c.id, username: c.username, name: c.name, avatar: c.avatar || '', members: Array.isArray(c.members) ? c.members.length : 0, isOwner, lastText: last ? last.text : '', lastAt: last ? last.createdAt : c.createdAt, unread: 0 };
        });
    const chatsList = readChats()
        .filter(c => (c.members || []).some(m => m.toLowerCase() === user))
        .map(c => {
            const last = c.messages && c.messages.length ? c.messages[c.messages.length - 1] : null;
            let unread = 0;
            (c.messages || []).forEach(m => {
                if (m.from.toLowerCase() === user) return;
                if (!Array.isArray(m.read)) return;
                if (!m.read.some(u => u.toLowerCase() === user)) unread++;
            });
            return { type: 'chat', id: c.id, name: c.name, avatar: '', members: (c.members || []).length, isOwner: c.owner.toLowerCase() === user, lastText: last ? (last.from + ': ' + last.text) : '', lastAt: last ? last.createdAt : c.createdAt, unread };
        });
    const all = channelsList.concat(chatsList).sort((a, b) => new Date(b.lastAt) - new Date(a.lastAt));
    sendJSON(res, 200, { items: all });
}
function handleCommunicationUnreadCount(req, res, query) {
    const me = authUser(req);
    if (!me) return sendJSON(res, 401, { error: 'Не авторизован' });
    const user = me.username.toLowerCase();
    let count = 0;
    readChats().forEach(c => {
        if (!(c.members || []).some(m => m.toLowerCase() === user)) return;
        (c.messages || []).forEach(m => {
            if (m.from.toLowerCase() === user) return;
            if (!Array.isArray(m.read)) return;
            if (!m.read.some(u => u.toLowerCase() === user)) count++;
        });
    });
    sendJSON(res, 200, { count });
}

/* ========== SERVER ========== */

const server = http.createServer(function (req, res) {
    const parsedUrl = parseUrl(req.url, true);
    const url = parsedUrl.pathname;
    const query = parsedUrl.query;

    if (req.method === 'OPTIONS') {
        res.writeHead(204, {
            'Access-Control-Allow-Origin': '*',
            'Access-Control-Allow-Headers': 'Content-Type, Authorization',
            'Access-Control-Allow-Methods': 'GET, POST, DELETE, OPTIONS'
        });
        res.end();
        return;
    }

    // Auth
    if (url === '/api/register' && req.method === 'POST') return handleRegister(req, res);
    if (url === '/api/login' && req.method === 'POST') return handleLogin(req, res);
    if (url === '/api/auth/google' && req.method === 'POST') return handleGoogleAuth(req, res);
    if (url === '/api/logout' && req.method === 'POST') return handleLogout(req, res);
    if (url === '/api/auth/session' && req.method === 'GET') return handleSession(req, res);

    // Users
    if (url === '/api/users' && req.method === 'GET') return handleUsersList(req, res);
    if (url === '/api/update-profile' && req.method === 'POST') return handleUpdateProfile(req, res);
    if (url === '/api/users/search' && req.method === 'GET') return handleUserSearch(req, res, query);
    if (url === '/api/user/heartbeat' && req.method === 'POST') return handleHeartbeat(req, res);
    if (url === '/api/user/status' && req.method === 'GET') return handleUserStatus(req, res, query);

    // Calls
    if (url === '/api/call/signal' && req.method === 'POST') return handleCallSignalSend(req, res);
    if (url === '/api/call/poll' && req.method === 'GET') return handleCallSignalPoll(req, res, query);
    if (url === '/api/call/log' && req.method === 'POST') return handleCallLog(req, res);

    // Friends
    if (url === '/api/friends/action' && req.method === 'POST') return handleFriendAction(req, res);
    if (url === '/api/friends/status' && req.method === 'GET') return handleFriendStatus(req, res, query);
    if (url === '/api/friends' && req.method === 'GET') return handleFriendsGet(req, res, query);

    // Block
    if (url === '/api/users/block' && req.method === 'POST') return handleBlockToggle(req, res);
    if (url === '/api/users/blocked' && req.method === 'GET') return handleBlockedList(req, res, query);
    if (url === '/api/users/block-status' && req.method === 'GET') return handleBlockStatus(req, res, query);

    // Channels
    if (url === '/api/channels' && req.method === 'GET') return handleChannelGet(req, res, query);
    if (url === '/api/channels' && req.method === 'POST') return handleChannelCreate(req, res);
    if (url === '/api/channels/update' && req.method === 'POST') return handleChannelUpdate(req, res);
    if (url === '/api/channels/subscribe' && req.method === 'POST') return handleChannelSubscribe(req, res);
    if (url === '/api/channels/search' && req.method === 'GET') return handleChannelSearch(req, res, query);
    if (url === '/api/channels/messages' && req.method === 'GET') return handleChannelMessagesGet(req, res, query);
    if (url === '/api/channels/message' && req.method === 'POST') return handleChannelMessageCreate(req, res);
    if (url === '/api/channels/message/reaction' && req.method === 'POST') return handleChannelMessageReaction(req, res);
    if (url === '/api/channels/message/delete' && req.method === 'POST') return handleChannelMessageDelete(req, res);
    if (url === '/api/channels/pin' && req.method === 'POST') return handleChannelPin(req, res);

    // Chats
    if (url === '/api/chats' && req.method === 'GET') return handleChatsGet(req, res, query);
    if (url === '/api/chats' && req.method === 'POST') return handleChatCreate(req, res);
    if (url === '/api/chats/messages' && req.method === 'GET') return handleChatMessagesGet(req, res, query);
    if (url === '/api/chats/message' && req.method === 'POST') return handleChatMessageCreate(req, res);
    if (url === '/api/chats/message/delete' && req.method === 'POST') return handleChatMessageDelete(req, res);
    if (url === '/api/chats/pin' && req.method === 'POST') return handleChatPin(req, res);

    // Posts
    if (url === '/api/posts/feed' && req.method === 'GET') return handleFeedGet(req, res, query);
    if (url === '/api/posts' && req.method === 'GET') return handlePostsGet(req, res, query);
    if (url === '/api/posts' && req.method === 'POST') return handlePostsCreate(req, res);
    if (url === '/api/posts/like' && req.method === 'POST') return handlePostLike(req, res);
    if (url === '/api/posts/comment' && req.method === 'POST') return handlePostComment(req, res);
    if (url === '/api/posts/comments' && req.method === 'GET') return handleCommentsGet(req, res, query);
    if (url === '/api/posts/repost' && req.method === 'POST') return handlePostRepost(req, res);
    if (url === '/api/posts/delete' && req.method === 'POST') return handlePostDelete(req, res);
    if (url === '/api/posts/comment/delete' && req.method === 'POST') return handleCommentDelete(req, res);

    // DM
    if (url === '/api/dm' && req.method === 'GET') return handleDmGet(req, res, query);
    if (url === '/api/dm' && req.method === 'POST') return handleDmCreate(req, res);
    if (url === '/api/dm/forward' && req.method === 'POST') return handleForward(req, res);
    if (url === '/api/dm/delete' && req.method === 'POST') return handleDmDelete(req, res);
    if (url === '/api/dm/conversations' && req.method === 'GET') return handleDmConversations(req, res, query);
    if (url === '/api/dm/unread-count' && req.method === 'GET') return handleDmUnreadCount(req, res, query);

    // Communication
    if (url === '/api/communication' && req.method === 'GET') return handleCommunication(req, res, query);
    if (url === '/api/communication/unread-count' && req.method === 'GET') return handleCommunicationUnreadCount(req, res, query);

    if (url.indexOf('/uploads/') === 0 && req.method === 'GET') return serveUpload(req, res, url);

    if (url === '/' || url === '/index.html') {
        try {
            const html = fs.readFileSync(HTML_FILE, 'utf8');
            res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'X-Content-Type-Options': 'nosniff', 'X-Frame-Options': 'DENY', 'Content-Security-Policy': "frame-ancestors 'none'", 'Referrer-Policy': 'strict-origin-when-cross-origin' });
            res.end(html);
        } catch (e) {
            res.writeHead(500, { 'Content-Type': 'text/plain; charset=utf-8' });
            res.end('index.html не найден рядом с server.js');
        }
        return;
    }

    sendJSON(res, 404, { error: 'Не найдено' });
});

server.listen(PORT, '0.0.0.0', function () {
    console.log('');
    console.log('🔥 Сервер Hot успешно запущен!');
    console.log('👉 Открой в браузере: http://localhost:' + PORT);
    console.log('');
});