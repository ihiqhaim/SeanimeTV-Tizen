/**
 * Seanime TV Client for Tizen TV 4.0
 * Verified against Seanime 3.10.3
 *
 * Authentication:
 *   - HTTP: X-Seanime-Token header = SHA-256(password)
 *   - HTTP requests also send the persistent client ID and any proof returned
 *     by Seanime, so the server can establish/refresh the client identity.
 *   - WebSocket: connect to Seanime's /events endpoint with clientId and the
 *     server-issued proof (when available). Do not put the password in a URL.
 *
 * Torrent streaming flow:
 *   1. Authenticate with HTTP and capture client identity response headers
 *   2. Open one shared WebSocket connection to /events
 *   3. POST /torrentstream/start (playbackType: "externalPlayerLink")
 *   4. Server pushes an "external-player-open-url" event with the stream URL
 *   5. Play that URL with AVPlay
 *
 * Transcoding fallback (Tizen 4 cannot decode AV1 / some 10-bit HEVC):
 *   - The file is always tried natively first.
 *   - If AVPlay reports NOT_SUPPORTED_VIDEO_CODEC / _FILE / _VIDEO_RESOLUTION (from prepareAsync or
 *     onerror), playback restarts at the same position through Seanime's media-streaming transcoder:
 *     POST /mediastream/request {streamType:'transcode'} -> HLS master playlist -> AVPlay.
 *   - A torrent session stays alive during the switch; its stream URL is what the server transcodes.
 *   - Settings -> "Transcode unsupported video" turns the fallback off.
 */

(function () {
    'use strict';

    // Console output is slow on a TV (and JSON.stringify of a large API reply is slower still).
    // Set DEBUG to true while developing; the shipped app stays quiet.
    // `DEBUG && console.log(...)` also skips evaluating the arguments when DEBUG is off.
    var DEBUG = false;

    // In-memory copy of the settings kept in localStorage (localStorage reads are
    // synchronous and slow on Tizen, and getSetting() runs once per poster card).
    var prefCache = {};

    // ===== Polyfills for Tizen 4.0 =====
    if (!String.prototype.padStart) {
        String.prototype.padStart = function (targetLength, padString) {
            targetLength = targetLength >> 0;
            padString = String(typeof padString !== 'undefined' ? padString : ' ');
            if (this.length >= targetLength) return String(this);
            targetLength = targetLength - this.length;
            if (targetLength > padString.length) {
                padString += padString.repeat(targetLength / padString.length);
            }
            return padString.slice(0, targetLength) + String(this);
        };
    }
    if (!String.prototype.repeat) {
        String.prototype.repeat = function (count) {
            count = count >> 0;
            if (count < 0) throw new RangeError('Invalid count value');
            if (count === 0 || this.length === 0) return '';
            var result = '', str = String(this);
            while (count > 0) {
                if (count & 1) result += str;
                count >>= 1;
                if (count) str += str;
            }
            return result;
        };
    }

    // ===== SHA-256 (pure JS) =====
    function sha256(ascii) {
        function rightRotate(value, amount) {
            return (value >>> amount) | (value << (32 - amount));
        }
        var mathPow = Math.pow;
        var maxWord = mathPow(2, 32);
        var lengthProperty = 'length';
        var i, j;
        var result = '';
        var words = [];
        var asciiBitLength = ascii[lengthProperty] * 8;

        var hash = sha256.h = sha256.h || [];
        var k = sha256.k = sha256.k || [];
        var primeCounter = k[lengthProperty];
        var isComposite = {};

        for (var candidate = 2; primeCounter < 64; candidate++) {
            if (!isComposite[candidate]) {
                for (i = 0; i < 313; i += candidate) isComposite[i] = candidate;
                hash[primeCounter] = (mathPow(candidate, 0.5) * maxWord) | 0;
                k[primeCounter++] = (mathPow(candidate, 1 / 3) * maxWord) | 0;
            }
        }

        ascii += '\x80';
        while (ascii[lengthProperty] % 64 - 56) ascii += '\x00';
        for (i = 0; i < ascii[lengthProperty]; i++) {
            j = ascii.charCodeAt(i);
            if (j >> 8) return '';
            words[i >> 2] |= j << ((3 - i) % 4) * 8;
        }
        words[words[lengthProperty]] = ((asciiBitLength / maxWord) | 0);
        words[words[lengthProperty]] = (asciiBitLength);

        for (j = 0; j < words[lengthProperty];) {
            var w = words.slice(j, j += 16);
            var oldHash = hash;
            hash = hash.slice(0, 8);

            for (i = 0; i < 64; i++) {
                var w15 = w[i - 15], w2 = w[i - 2];
                var a = hash[0], e = hash[4];
                var temp1 = hash[7]
                    + (rightRotate(e, 6) ^ rightRotate(e, 11) ^ rightRotate(e, 25))
                    + ((e & hash[5]) ^ ((~e) & hash[6]))
                    + k[i]
                    + (w[i] = (i < 16) ? w[i] : (
                        w[i - 16]
                        + (rightRotate(w15, 7) ^ rightRotate(w15, 18) ^ (w15 >>> 3))
                        + w[i - 7]
                        + (rightRotate(w2, 17) ^ rightRotate(w2, 19) ^ (w2 >>> 10))
                    ) | 0);
                var temp2 = (rightRotate(a, 2) ^ rightRotate(a, 13) ^ rightRotate(a, 22))
                    + ((a & hash[1]) ^ (a & hash[2]) ^ (hash[1] & hash[2]));
                hash = [(temp1 + temp2) | 0].concat(hash);
                hash[4] = (hash[4] + temp1) | 0;
            }
            for (i = 0; i < 8; i++) hash[i] = (hash[i] + oldHash[i]) | 0;
        }

        for (i = 0; i < 8; i++) {
            for (j = 3; j + 1; j--) {
                var b = (hash[i] >> (j * 8)) & 255;
                result += ((b < 16) ? 0 : '') + b.toString(16);
            }
        }
        return result;
    }

    var booted = false;

    window.addEventListener('error', function (event) {
        console.error('[Global Error]', event.message, 'at', event.filename + ':' + event.lineno);
    });

    function logJSON(label, obj, maxLen) {
        if (!DEBUG) return;
        maxLen = maxLen || 4000;
        try {
            var str = JSON.stringify(obj);
            if (str && str.length > maxLen) str = str.slice(0, maxLen) + '...[truncated]';
            DEBUG && console.log(label, str);
        } catch (e) { DEBUG && console.log(label, obj); }
    }

    function unwrapData(data) {
        if (data && typeof data === 'object' && !Array.isArray(data) && 'data' in data) {
            return data.data;
        }
        return data;
    }

    function deepUnwrap(data) {
        var d = data;
        var guard = 0;
        while (d && typeof d === 'object' && !Array.isArray(d) &&
               'data' in d && d.data !== null && guard < 3) {
            d = d.data;
            guard++;
        }
        return d;
    }

    // ===== Configuration =====
    var STORAGE_KEYS = {
        SERVER_URL: 'seanime_server_url',
        SERVER_PASSWORD: 'seanime_server_password',
        PASSWORD_HASH: 'seanime_password_hash',
        SETUP_COMPLETE: 'seanime_setup_complete',
        CLIENT_ID: 'seanime_client_id',
        SERVER_CLIENT_ID: 'seanime_server_client_id',
        SERVER_CLIENT_ID_PROOF: 'seanime_server_client_id_proof'
    };

    // ===== Credential storage =====
    // The plaintext password is never stored. Seanime authenticates with
    // sha256(password), so that hash is stored instead; it is just as
    // sensitive (anyone holding it can use the server), which is why it lives
    // in the app's private storage and can be kept for this session only
    // ("Stay signed in" = Off in Settings keeps it in sessionStorage).
    function staySignedIn() {
        try { return localStorage.getItem('seanime_pref_set_staySignedIn') !== 'off'; } catch (e) { return true; }
    }
    function credStore() { return staySignedIn() ? localStorage : sessionStorage; }
    function credOther() { return staySignedIn() ? sessionStorage : localStorage; }
    function credGet(key) {
        try {
            var v = credStore().getItem(key);
            return v != null ? v : credOther().getItem(key);
        } catch (e) { return null; }
    }
    function credSet(key, value) {
        try { credStore().setItem(key, value); credOther().removeItem(key); } catch (e) {}
    }
    function credRemove(key) {
        try { localStorage.removeItem(key); sessionStorage.removeItem(key); } catch (e) {}
    }
    // Older versions stored the plaintext password: convert it to a hash and delete it.
    (function migrateLegacyPassword() {
        try {
            var legacy = localStorage.getItem(STORAGE_KEYS.SERVER_PASSWORD);
            if (legacy !== null) {
                if (legacy && credGet(STORAGE_KEYS.PASSWORD_HASH) === null) {
                    credSet(STORAGE_KEYS.PASSWORD_HASH, sha256(legacy));
                }
                localStorage.removeItem(STORAGE_KEYS.SERVER_PASSWORD);
            }
        } catch (e) {}
    })();

    var CONFIG = {
        serverUrl: localStorage.getItem(STORAGE_KEYS.SERVER_URL) || '',
        passwordHash: credGet(STORAGE_KEYS.PASSWORD_HASH) || '',
        apiPath: '/api/v1',
        defaultImage: 'data:image/svg+xml,' + encodeURIComponent(
            '<svg xmlns="http://www.w3.org/2000/svg" width="220" height="320" fill="#1a1a28">' +
            '<rect width="220" height="320" fill="#1a1a28"/>' +
            '<text x="110" y="160" text-anchor="middle" fill="#444" font-size="16">No Image</text></svg>'
        )
    };

    // ===== State =====
    var state = {
        currentScreen: 'setup',
        library: [],
        continueWatching: [],
        searchResults: [],
        currentAnime: null,
        episodes: [],
        playerReady: false,
        controlsVisible: true,
        controlsTimer: null,
        currentEpisodeIndex: 0,
        isPlaying: false,
        activeStreamMediaId: null,
        activeStreamEpisode: null,
        activeSessionId: null,
        // playback / progress
        playbackToken: 0,
        avplayOpen: false,
        playbackOrigin: 'detail',
        currentEpisodeNumber: 0,
        episodesMediaId: null,
        progressSynced: false,
        progressRetryAt: 0,
        lastContinuitySave: 0,
        upNext: null,
        listProgress: {},
        listProgressLoaded: false,
        profileStats: null,          // per-status counts from the AniList collection (see profileComputeStats)
        profileStatsLoading: false,
        needsRefresh: false,
        // audio / subtitle tracks
        tracks: { audio: [], text: [] },
        audioIndex: null,
        textIndex: -1,
        subRender: 'app',     // how the selected embedded track is drawn: 'app' | 'tv'
        subGot: false,        // the TV has delivered subtitle text since the track was selected
        osdProgress: null,    // last values for the OSD time labels / bar
        subWatchMs: 0,        // playing time spent waiting for that first text
        appCues: [],          // cues the app is showing right now: [{text, until}] (media ms)
        trackPanelKind: null,
        // navigation / settings / discover
        view: 'home',
        lastCard: null,
        settingsDirty: false,
        discoverLoadedAt: 0,
        discoverSeq: 0,
        // session
        loggingIn: false,
        signingOut: false,
        // playback sources / errors
        playbackKind: 'torrent',
        playbackMediaId: null,
        lastPlayback: null,
        playerError: null,
        autoRetries: 0,
        buffering: false,
        bufferingSince: 0,
        bundle: null,
        // detail screen / my list
        detail: null,
        listEdit: null,
        listEntries: {},
        extCues: null,
        scheduleLoadedAt: 0,
        blockedIds: {},
        detailStack: [],
        picker: null,
        playerErrorInfo: null,
        // scrub / speed / skip / torrent start-up feedback
        scrub: null,              // pending scrub: { from, target, dur, ... } (ms)
        lastSeek: null,           // { ms, at } of the last absolute seek (the TV reports the old time for a moment)
        speedApplied: false,      // AVPlay is running at a speed other than 1x
        skipData: { aniskip: [], chapters: [] },
        skipShown: null,          // the segment the Skip button is offering right now
        torrentInfo: null,        // latest numbers from the server's torrentstream events
        loadingSince: 0,
        bufferingPercent: 0,
        transcoding: false,        // the current playback goes through the server's transcoder
        // P0 phases
        libFilter: 'ALL',            // ALL | CURRENT | PLANNING | COMPLETED | PAUSED | DROPPED | REPEATING
        libSearch: '',
        libSort: 'updated',          // updated | title | score | progress
        libCustom: [],               // custom lists from /anilist/collection
        discPage: 1,
        discTotal: 0,
        discFilters: { genre: '', format: '', status: '', sort: 'POPULARITY_DESC', year: '' }
    };

    var heroState = { items: [], currentIndex: 0, rotationTimer: null };

    function $(sel) { return document.querySelector(sel); }

    function showScreen(name) {
        var all = document.querySelectorAll('.screen');
        for (var i = 0; i < all.length; i++) all[i].classList.remove('active');
        var target = document.getElementById(name + '-screen');
        if (target) {
            target.classList.add('active');
            state.currentScreen = name;
            DEBUG && console.log('[Screen] ->', name);
            imgSchedule(60);
            if (name === 'home' && state.needsRefresh) {
                state.needsRefresh = false;
                setTimeout(function () { loadLibrary(); }, 0);
            }
        }
    }

    // ===== Key Codes =====
    var KEY_CODES = {
        LEFT: 37, UP: 38, RIGHT: 39, DOWN: 40,
        ENTER: 13, RETURN: 10009, ESCAPE: 27,
        PLAY: 415, PAUSE: 19, STOP: 413,
        REWIND: 412, FORWARD: 417,
        RED: 403, GREEN: 404, YELLOW: 405, BLUE: 406
    };

    // ===== HMAC stream tokens =====
    // AVPlay cannot send an X-Seanime-Token header, so streams that are not
    // announced by the server (local files) carry a short signed token in the
    // URL, exactly like Seanime's own web UI creates them:
    //   token = base64url(claims) + "." + base64url(HMAC-SHA256(claims_b64, secret))
    // where the secret is the server password hash and claims = {endpoint, iat, exp}.
    function hexToBin(hex) {
        var out = '';
        for (var i = 0; i < hex.length; i += 2) out += String.fromCharCode(parseInt(hex.substr(i, 2), 16));
        return out;
    }
    function hmacSha256Bin(key, msg) {
        if (key.length > 64) key = hexToBin(sha256(key));
        while (key.length < 64) key += '\0';
        var ipad = '', opad = '';
        for (var i = 0; i < 64; i++) {
            ipad += String.fromCharCode(key.charCodeAt(i) ^ 0x36);
            opad += String.fromCharCode(key.charCodeAt(i) ^ 0x5c);
        }
        return hexToBin(sha256(opad + hexToBin(sha256(ipad + msg))));
    }
    function b64url(binary) {
        return btoa(binary).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
    }
    function makeHmacToken(endpoint) {
        var now = Math.floor(Date.now() / 1000);
        // long lifetime: the TV's clock may be a bit off and the server only checks "exp"
        var claims = b64url(JSON.stringify({ endpoint: endpoint, iat: now, exp: now + 7 * 24 * 3600 }));
        return claims + '.' + b64url(hmacSha256Bin(CONFIG.passwordHash, claims));
    }

    // URL AVPlay can open for a file in the server's library (same URL Seanime's web UI copies).
    function buildLocalStreamUrl(path) {
        var endpoint = CONFIG.apiPath + '/mediastream/file';
        var url = CONFIG.serverUrl + endpoint + '?path=' + encodeURIComponent(path);
        if (CONFIG.passwordHash) url += '&token=' + encodeURIComponent(makeHmacToken(endpoint));
        return url;
    }

    // ===== OSD icons (white, shadow comes from CSS) =====
    var ICON_PLAY  = '<svg viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><path d="M8 5.2v13.6a1 1 0 0 0 1.5.86l11-6.8a1 1 0 0 0 0-1.72l-11-6.8A1 1 0 0 0 8 5.2z"/></svg>';
    var ICON_PAUSE = '<svg viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><rect x="6" y="5" width="4.2" height="14" rx="1.2"/><rect x="13.8" y="5" width="4.2" height="14" rx="1.2"/></svg>';

    // ===== Client ID helpers =====
    function getClientId() {
        var id = localStorage.getItem(STORAGE_KEYS.CLIENT_ID);
        if (!id) {
            id = 'tizen-tv-' + Math.random().toString(36).slice(2, 10);
            localStorage.setItem(STORAGE_KEYS.CLIENT_ID, id);
        }
        return id;
    }

    var identityHeaderDiagnosticLogged = false;

    function captureServerClientId(response) {
        if (!response || !response.headers) return;
        try {
            var id = response.headers.get('X-Seanime-Client-Id') || '';
            var proof = response.headers.get('X-Seanime-Client-Id-Proof') || '';

            if (id) {
                if (localStorage.getItem(STORAGE_KEYS.SERVER_CLIENT_ID) !== id) {
                    DEBUG && console.log('[Auth] Captured server client ID.');
                }
                localStorage.setItem(STORAGE_KEYS.SERVER_CLIENT_ID, id);
            }
            if (proof) {
                localStorage.setItem(STORAGE_KEYS.SERVER_CLIENT_ID_PROOF, proof);
            }

            // Never print the identity proof itself. Only report whether the
            // headers are readable, which distinguishes a client issue from
            // a server-version / CORS-exposure issue.
            if ((!id || !proof) && !identityHeaderDiagnosticLogged) {
                identityHeaderDiagnosticLogged = true;
                var names = [];
                if (response.headers.forEach) {
                    response.headers.forEach(function (value, name) {
                        if (/seanime|client-id/i.test(name)) names.push(name);
                    });
                }
                console.warn('[Auth] Server identity headers: id=' + (!!id) +
                    ', proof=' + (!!proof) + ', visible=' +
                    (names.length ? names.join(', ') : '(none)'));
            }
        } catch (e) {
            if (!identityHeaderDiagnosticLogged) {
                identityHeaderDiagnosticLogged = true;
                console.warn('[Auth] Could not inspect server identity headers:', e.message || e);
            }
        }
    }

    function getServerClientId() {
        return localStorage.getItem(STORAGE_KEYS.SERVER_CLIENT_ID) || '';
    }

    function getServerClientIdProof() {
        return localStorage.getItem(STORAGE_KEYS.SERVER_CLIENT_ID_PROOF) || '';
    }

    // ===== WebSocket Manager =====
    var ws = null;
    var wsListeners = [];
    var wsReconnectTimer = null;
    var wsConnectPromise = null;
    var wsManualClose = false;

    function wsBaseUrl() {
        var base = CONFIG.serverUrl.replace(/\/+$/, '');
        return base.replace(/^http:/, 'ws:').replace(/^https:/, 'wss:');
    }

    function buildWsVariants() {
        // Seanime 3.10.3 /events (internal/handlers/websocket.go):
        //   - when a server password is set, the handshake REQUIRES
        //     ?token=<sha256(password)>. Browsers cannot send custom headers
        //     on a WebSocket, and cookies are not usable from a file://
        //     origin, so the query string is the only way in.
        //   - the identity query params are "id" and "proof" (not "clientId").
        var url = wsBaseUrl().replace(/\/+$/, '') + '/events';
        var params = [];
        if (CONFIG.passwordHash) {
            params.push('token=' + encodeURIComponent(CONFIG.passwordHash));
        }
        var serverClientId = getServerClientId();
        var proof = getServerClientIdProof();
        if (serverClientId && proof) {
            params.push('id=' + encodeURIComponent(serverClientId));
            params.push('proof=' + encodeURIComponent(proof));
        }
        return [url + (params.length ? '?' + params.join('&') : '')];
    }

    function connectWebSocket() {
        if (ws && ws.readyState === WebSocket.OPEN) {
            return Promise.resolve();
        }
        if (wsConnectPromise) {
            return wsConnectPromise;
        }

        if (ws && ws.readyState !== WebSocket.CLOSED) {
            try { ws.close(); } catch (e) {}
        }
        ws = null;
        wsManualClose = false;
        wsClientIdentityReady = false;

        wsConnectPromise = new Promise(function (resolve, reject) {
            var url = buildWsVariants()[0];
            var displayUrl = url.replace(/([?&](?:proof|token)=)[^&]+/g, '$1***');
            DEBUG && console.log('[WS] Connecting to:', displayUrl);

            var socket;
            var settled = false;
            var opened = false;
            var timeout = null;

            function fail(error) {
                if (settled) return;
                settled = true;
                if (timeout) clearTimeout(timeout);
                try { if (socket) socket.close(); } catch (e) {}
                if (ws === socket) ws = null;
                reject(error);
            }

            try {
                socket = new WebSocket(url);
            } catch (e) {
                fail(new Error('Could not create WebSocket: ' + (e.message || e)));
                return;
            }

            timeout = setTimeout(function () {
                fail(new Error('WebSocket connection timed out. Check the /events endpoint and client proof.'));
            }, 10000);

            socket.onopen = function () {
                if (settled) {
                    try { socket.close(); } catch (e) {}
                    return;
                }
                settled = true;
                opened = true;
                if (timeout) clearTimeout(timeout);
                ws = socket;
                socket.onmessage = onWsMessage;
                socket.onerror = function (event) {
                    console.warn('[WS] Socket error event:', event && event.message ? event.message : 'connection error');
                };
                socket.onclose = function (event) {
                    if (ws === socket) ws = null;
                    if (opened) onWsClose(event);
                };
                DEBUG && console.log('[WS] Connected to /events');
                onSocketOpen();
                resolve();
            };

            socket.onerror = function () {
                // The browser's WebSocket API does not expose HTTP handshake
                // status/body. Wait for close/timeout and report one error.
            };

            socket.onclose = function (event) {
                if (opened) {
                    if (ws === socket) ws = null;
                    onWsClose(event);
                    return;
                }
                if (!settled) {
                    settled = true;
                    if (timeout) clearTimeout(timeout);
                    reject(new Error(
                        'WebSocket handshake rejected (close code ' + (event.code || '?') + '). ' +
                        'Verify Seanime /events authentication and allow the authentication rate limit to reset.'
                    ));
                }
            };
        });

        // Clear the shared promise whether it succeeds or fails, without relying
        // on Promise.finally (older Tizen WebKit compatibility).
        wsConnectPromise = wsConnectPromise.then(function () {
            wsConnectPromise = null;
        }, function (error) {
            wsConnectPromise = null;
            throw error;
        });
        return wsConnectPromise;
    }

    // The server pushes {type:"client-identity", payload:{clientId, proof}}
    // right after the handshake. HTTP calls must then carry that same
    // id + proof so the server routes torrent events to THIS socket.
    var wsClientIdentityReady = false;
    var wsIdentityWaiters = [];

    function handleClientIdentity(msg) {
        var p = msg && msg.payload;
        if (!p || !p.clientId) return;
        localStorage.setItem(STORAGE_KEYS.SERVER_CLIENT_ID, p.clientId);
        if (p.proof) localStorage.setItem(STORAGE_KEYS.SERVER_CLIENT_ID_PROOF, p.proof);
        wsClientIdentityReady = true;
        DEBUG && console.log('[WS] Client identity received (proof ' + (p.proof ? 'present' : 'missing') + ').');
        var waiters = wsIdentityWaiters.slice();
        wsIdentityWaiters = [];
        waiters.forEach(function (w) { w(); });
    }

    function waitForClientIdentity(timeoutMs) {
        timeoutMs = timeoutMs || 8000;
        if (wsClientIdentityReady) return Promise.resolve();
        return new Promise(function (resolve, reject) {
            var timer = setTimeout(function () {
                var i = wsIdentityWaiters.indexOf(done);
                if (i >= 0) wsIdentityWaiters.splice(i, 1);
                reject(new Error('WebSocket connected but the server never sent a client identity.'));
            }, timeoutMs);
            function done() { clearTimeout(timer); resolve(); }
            wsIdentityWaiters.push(done);
        });
    }

    function onWsMessage(event) {
        wsLastActivity = Date.now();
        var raw = event.data;
        // The server pushes every log line over this socket. Parsing them is wasted work unless a
        // stream is starting (then they are only logged). Pongs only needed the timestamp above.
        if (typeof raw === 'string') {
            if (raw.indexOf('"type":"pong"') !== -1) return;
            if (!state.activeStreamMediaId && raw.indexOf('"type":"console-log"') !== -1) return;
        }
        var msg = raw;
        try { msg = JSON.parse(raw); } catch (e) { /* keep as string */ }
        var mtype = msg && msg.type;
        if (mtype !== 'console-log' && mtype !== 'pong') DEBUG && console.log('[WS] <<', mtype || raw);
        if (mtype === 'pong') return;
        if (mtype === 'client-identity') handleClientIdentity(msg);
        // Server log lines are pushed over the socket; they explain why a
        // torrent search/selection failed. Show them while a stream starts.
        if (mtype === 'console-log' && state.activeStreamMediaId) {
            var line = typeof msg.payload === 'string' ? msg.payload : JSON.stringify(msg.payload);
            DEBUG && console.log('[Server]', (line || '').slice(0, 400));
        }

        wsListeners.forEach(function (fn) {
            try { fn(msg); } catch (e) { console.warn('[WS] listener error:', e); }
        });

        handleWsTorrentEvent(msg);
    }

    // ----- Reconnect loop, heartbeat and connection status -----
    var wsDesired = false;          // true while signed in: the socket should be kept alive
    var wsBackoffIdx = 0;
    var wsHeartbeatTimer = null;
    var wsLastActivity = 0;
    var WS_BACKOFF = [1000, 2000, 4000, 8000, 15000, 30000];
    var HEARTBEAT_EVERY = 15000;
    var HEARTBEAT_DEAD_AFTER = 45000;
    var connectionOnline = null;
    var appToastTimer = null;

    function setConnectionStatus(online) {
        if (connectionOnline === online) return;
        var wasOnline = connectionOnline;
        connectionOnline = online;
        var s = $('#connection-status');
        if (s) s.className = 'status-dot ' + (online ? 'online' : 'offline');
        if (wasOnline === false && online) showAppToast('Connection restored');
        else if (wasOnline === true && !online) showAppToast('Connection lost \u2014 reconnecting\u2026', 4000);
    }

    function showAppToast(text, ms) {
        var el = $('#app-toast');
        if (!el) return;
        el.textContent = text;
        el.classList.add('show');
        if (appToastTimer) clearTimeout(appToastTimer);
        appToastTimer = setTimeout(function () { el.classList.remove('show'); }, ms || 3000);
    }

    function onSocketOpen() {
        wsBackoffIdx = 0;
        setConnectionStatus(true);
        startHeartbeat();
    }

    function startHeartbeat() {
        stopHeartbeat();
        wsLastActivity = Date.now();
        wsHeartbeatTimer = setInterval(function () {
            if (!ws || ws.readyState !== 1) return;
            if (Date.now() - wsLastActivity > HEARTBEAT_DEAD_AFTER) {
                // half-open connection (e.g. Wi-Fi dropped): the browser never reports it
                console.warn('[WS] No traffic for ' + (HEARTBEAT_DEAD_AFTER / 1000) + 's, reconnecting');
                dropSocket();
                return;
            }
            try { ws.send(JSON.stringify({ type: 'ping', payload: { timestamp: Date.now() } })); } catch (e) {}
        }, HEARTBEAT_EVERY);
    }
    function stopHeartbeat() {
        if (wsHeartbeatTimer) { clearInterval(wsHeartbeatTimer); wsHeartbeatTimer = null; }
    }
    function dropSocket() {
        var s = ws;
        ws = null;
        if (s) { s.onclose = null; s.onmessage = null; try { s.close(); } catch (e) {} }
        onWsClose({ code: 4000 });
    }

    function onWsClose(event) {
        DEBUG && console.log('[WS] Closed', event && event.code ? '(code ' + event.code + ')' : '');
        stopHeartbeat();
        ws = null;
        wsClientIdentityReady = false;
        if (wsManualClose) return;
        scheduleReconnect('closed');
    }

    // Asks the server whether we are still signed in:
    //   'ok' | 'unauthenticated' (password changed) | 'unreachable'
    function probeSession() {
        return api.request('/status').then(function (data) {
            var d = unwrapData(data);
            if (CONFIG.passwordHash && d && d.user === null) return 'unauthenticated';
            return 'ok';
        }, function (e) {
            if (/HTTP 401/.test(e.message || '')) return 'unauthenticated';
            return 'unreachable';
        });
    }

    function scheduleReconnect(reason, immediate) {
        if (!wsDesired) return;
        if (wsReconnectTimer) {
            if (!immediate) return;
            clearTimeout(wsReconnectTimer);
            wsReconnectTimer = null;
        }
        var delay = immediate ? 0 : WS_BACKOFF[Math.min(wsBackoffIdx, WS_BACKOFF.length - 1)];
        if (!immediate) wsBackoffIdx++;
        if (!immediate) setConnectionStatus(false);
        DEBUG && console.log('[WS] Reconnecting in ' + delay + 'ms (' + reason + ')');
        wsReconnectTimer = setTimeout(function () {
            wsReconnectTimer = null;
            if (!wsDesired) return;
            probeSession().then(function (result) {
                if (!wsDesired) return;
                if (result === 'unauthenticated') { handleSessionExpired('probe'); return; }
                if (result === 'unreachable') { setConnectionStatus(false); scheduleReconnect('server unreachable'); return; }
                connectWebSocket().catch(function (e) {
                    console.warn('[WS] Reconnect failed:', e.message);
                    scheduleReconnect('connect failed');
                });
            });
        }, delay);
    }

    function startSocketLoop() {
        wsDesired = true;
        wsBackoffIdx = 0;
        connectWebSocket().catch(function (e) {
            console.warn('[WS] Initial connect failed:', e.message);
            scheduleReconnect('initial connect failed');
        });
    }

    function stopSocketLoop() {
        wsDesired = false;
        closeWebSocket();
    }

    function closeWebSocket() {
        wsManualClose = true;
        stopHeartbeat();
        if (wsReconnectTimer) { clearTimeout(wsReconnectTimer); wsReconnectTimer = null; }
        if (ws) {
            var socket = ws;
            ws = null;
            try { socket.close(); } catch (e) {}
        }
        wsConnectPromise = null;
    }

    // ----- Periodic session / server health check -----
    var healthTimer = null;
    var HEALTH_EVERY = 30000;
    function startHealthCheck() {
        stopHealthCheck();
        healthTimer = setInterval(function () {
            if (!wsDesired) return;
            probeSession().then(function (result) {
                if (!wsDesired) return;
                if (result === 'unauthenticated') {
                    // confirm once so a single glitch does not sign the user out
                    setTimeout(function () {
                        probeSession().then(function (again) {
                            if (wsDesired && again === 'unauthenticated') handleSessionExpired('health check');
                        });
                    }, 1500);
                } else if (result === 'unreachable') {
                    setConnectionStatus(false);
                } else {
                    setConnectionStatus(true);
                    if (!ws && !wsReconnectTimer && !wsConnectPromise) scheduleReconnect('socket missing', true);
                }
            });
        }, HEALTH_EVERY);
    }
    function stopHealthCheck() {
        if (healthTimer) { clearInterval(healthTimer); healthTimer = null; }
    }

    // The password changed on the server (or the saved login is otherwise
    // rejected): drop the saved login and ask for it again.
    function handleSessionExpired(reason) {
        if (state.signingOut || state.loggingIn) return;
        state.signingOut = true;
        console.warn('[Session] Expired:', reason);
        stopPlayback();
        stopHeroRotation();
        stopSocketLoop();
        stopHealthCheck();
        clearSession();
        CONFIG.passwordHash = '';
        setConnectionStatus(false);
        openSetupScreen();
        var err = $('#setup-error');
        if (err) err.textContent = 'Your session expired \u2014 the server password may have changed. Enter the current password.';
    }

    window.addEventListener('online', function () {
        if (wsDesired) scheduleReconnect('network back', true);
    });
    window.addEventListener('offline', function () {
        if (wsDesired) setConnectionStatus(false);
    });

    function addWsListener(fn) {
        wsListeners.push(fn);
        return function () {
            var i = wsListeners.indexOf(fn);
            if (i >= 0) wsListeners.splice(i, 1);
        };
    }

    // Handle torrentstream WS events globally
    var pendingStreamResolvers = [];

    function handleWsTorrentEvent(msg) {
        if (!msg || typeof msg !== 'object') return;
        var type = msg.type || (msg.data && msg.data.type);

        // playbackType "externalPlayerLink" delivers the stream here:
        //   {type:"external-player-open-url", payload:{url, mediaId, ...}}
        if (type === 'external-player-open-url') {
            var link = msg.payload && msg.payload.url;
            if (link) {
                link = rewriteStreamUrl(link);
                DEBUG && console.log('[WS] Stream URL from external-player-open-url');
                var rs = pendingStreamResolvers.slice();
                pendingStreamResolvers = [];
                rs.forEach(function (r) { r(link); });
            }
            return;
        }

        // Accept any torrentstream-related message
        if (typeof type !== 'string' || type.indexOf('torrentstream') !== 0) return;

        DEBUG && console.log('[WS] Torrent event:', type, JSON.stringify(msg).slice(0, 800));

        applyTorrentFeedback(msg);

        var url = extractStreamUrlFromWsMessage(msg);
        if (url) {
            url = rewriteStreamUrl(url);
            DEBUG && console.log('[WS] Stream URL from WS:', url);
            var resolvers = pendingStreamResolvers.slice();
            pendingStreamResolvers = [];
            resolvers.forEach(function (r) { r(url); });
        }
    }

    function extractStreamUrlFromWsMessage(msg) {
        if (!msg) return null;
        if (typeof msg === 'string') return msg;

        var candidates = [
            msg.streamUrl, msg.url, msg.stream_url, msg.link,
            msg.playbackUrl, msg.fileUrl
        ];

        ['data', 'payload', 'message'].forEach(function (k) {
            if (msg[k] && typeof msg[k] === 'object') {
                candidates.push(
                    msg[k].streamUrl, msg[k].url, msg[k].stream_url,
                    msg[k].link, msg[k].playbackUrl, msg[k].fileUrl
                );
                ['data', 'payload'].forEach(function (k2) {
                    if (msg[k][k2] && typeof msg[k][k2] === 'object') {
                        candidates.push(
                            msg[k][k2].streamUrl, msg[k][k2].url,
                            msg[k][k2].stream_url, msg[k][k2].link
                        );
                    }
                });
            }
        });

        for (var i = 0; i < candidates.length; i++) {
            if (candidates[i] && typeof candidates[i] === 'string') {
                return candidates[i];
            }
        }
        return null;
    }

    function rewriteStreamUrl(url) {
        if (!url) return url;
        // Seanime sends "{{SCHEME}}://{{HOST}}/api/v1/torrentstream/stream/..."
        // and expects the client to fill the placeholders in.
        var schemeMatch = CONFIG.serverUrl.match(/^(https?):\/\/([^\/]+)/i);
        if (schemeMatch) {
            url = url.replace(/\{\{SCHEME\}\}/g, schemeMatch[1].toLowerCase())
                     .replace(/\{\{HOST\}\}/g, schemeMatch[2])
                     .replace(/\{\{SERVER_URL\}\}/g, schemeMatch[1].toLowerCase() + '://' + schemeMatch[2]);
        }
        var host = CONFIG.serverUrl.replace(/^https?:\/\//, '').split(':')[0];
        if (host) {
            url = url.replace(/\/\/127\.0\.0\.1(:|$)/, '//' + host + '$1');
            url = url.replace(/\/\/localhost(:|$)/i, '//' + host + '$1');
        }
        return url;
    }

    function waitForStreamUrl(timeoutMs) {
        timeoutMs = timeoutMs || 90000;
        return new Promise(function (resolve, reject) {
            var done = false;
            var timer = setTimeout(function () {
                if (done) return;
                done = true;
                var i = pendingStreamResolvers.indexOf(wrapped);
                if (i >= 0) pendingStreamResolvers.splice(i, 1);
                reject(new Error('Timed out waiting for stream URL from WebSocket'));
            }, timeoutMs);

            function wrapped(url) {
                if (done) return;
                done = true;
                clearTimeout(timer);
                resolve(url);
            }

            pendingStreamResolvers.push(wrapped);
        });
    }

    // ===== Response shape helpers =====
    function extractTitleText(t) {
        if (!t) return 'Unknown';
        if (typeof t === 'string') return t;
        var pref = getSetting('titleLang');
        if (pref === 'romaji')  return t.romaji || t.english || t.native || t.userPreferred || 'Unknown';
        if (pref === 'english') return t.english || t.romaji || t.native || t.userPreferred || 'Unknown';
        if (pref === 'native')  return t.native || t.romaji || t.english || t.userPreferred || 'Unknown';
        return t.userPreferred || t.english || t.romaji || t.native || 'Unknown';
    }

    // Posters in rows are 220px wide: AniList's "large" (about 230px) is enough.
    // The much bigger "extraLarge" is only used for the single detail poster.
    function extractCardImage(img) {
        if (!img) return '';
        if (typeof img === 'string') return img;
        return img.large || img.medium || img.extraLarge || img.original || '';
    }

    function extractImageUrl(img) {
        if (!img) return '';
        if (typeof img === 'string') return img;
        return img.extraLarge || img.large || img.medium || img.original || '';
    }

    function extractLibraryEntries(data) {
        if (!data) return [];
        var d = unwrapData(data);
        if (!d) return [];
        if (Array.isArray(d)) return d;
        if (Array.isArray(d.lists)) {
            var out = [];
            d.lists.forEach(function (list) {
                if (list && Array.isArray(list.entries)) {
                    list.entries.forEach(function (entry) {
                        if (entry && typeof entry === 'object') {
                            entry._listType = list.type;
                            entry._listStatus = list.status;
                            if (entry.updatedAt == null && entry.updated_at != null) entry.updatedAt = entry.updated_at;
                            if (entry.media && entry.media.updatedAt == null && entry.media.updated_at != null) entry.media.updatedAt = entry.media.updated_at;
                            out.push(entry);
                        }
                    });
                }
            });
            return out;
        }
        if (Array.isArray(d.entries)) return d.entries;
        if (Array.isArray(d.items)) return d.items;
        if (d.collection) return extractLibraryEntries(d.collection);
        return [];
    }

    function extractContinueWatchingFromCollection(data) {
        if (!data) return [];
        var d = unwrapData(data);
        if (!d) return [];
        if (d.stream && Array.isArray(d.stream.continueWatchingList)) {
            return d.stream.continueWatchingList;
        }
        if (Array.isArray(d.continueWatchingList)) return d.continueWatchingList;
        if (Array.isArray(d.continueWatching)) return d.continueWatching;
        return [];
    }

    function extractContinueWatchingFromHomeItems(data) {
        if (!data) return [];
        var d = unwrapData(data);
        if (!d) return [];
        if (Array.isArray(d)) return d;
        var keys = ['continueWatching', 'continue_watching', 'watching',
                    'recentlyWatched', 'recently_watched', 'inProgress',
                    'in_progress', 'resume'];
        for (var i = 0; i < keys.length; i++) {
            if (Array.isArray(d[keys[i]])) return d[keys[i]];
        }
        return [];
    }

    // Adult/suggestive content is permanently hidden (no toggle). AniList isAdult + Hentai/Ecchi genres.
    var BLOCKED_GENRES = ['hentai', 'ecchi'];
    function isAdultMedia(m) {
        if (!m) return false;
        if (m.isAdult === true) return true;
        var g = m.genres;
        if (g && g.length) {
            for (var i = 0; i < g.length; i++) {
                if (BLOCKED_GENRES.indexOf(String(g[i]).toLowerCase()) >= 0) return true;
            }
        }
        return false;
    }

    function normalizeContinueWatching(raw) {
        if (!raw) return null;
        var anime = raw.baseAnime || raw.media || raw.anime || {};
        if (isAdultMedia(anime)) return null;
        var epMeta = raw.episodeMetadata || {};
        var episodeNumber = raw.episodeNumber != null ? raw.episodeNumber
                          : (raw.progressNumber != null ? raw.progressNumber : null);
        var duration = null;
        if (typeof raw.duration === 'number') duration = raw.duration;
        else if (typeof anime.duration === 'number') duration = anime.duration * 60;
        var progress = typeof raw.progress === 'number' ? raw.progress : null;

        return {
            mediaId: anime.id || raw.mediaId || raw.id,
            title: extractTitleText(anime.title || raw.title),
            coverImage: extractCardImage(anime.coverImage || anime.image) || '',
            posterLarge: extractImageUrl(anime.coverImage || anime.image) || '',
            bannerImage: anime.bannerImage ||
                         extractImageUrl(anime.coverImage || anime.image) || '',
            episodes: anime.episodes || null,
            format: anime.format || '',
            status: anime.status || '',
            genres: anime.genres || [],
            meanScore: anime.meanScore || null,
            year: anime.seasonYear || (anime.startDate && anime.startDate.year) || null,
            episodeLength: anime.duration || null,
            nextAiring: anime.nextAiringEpisode || null,
            description: anime.description || epMeta.summary || '',
            episodeNumber: episodeNumber,
            aniDbEpisode: raw.aniDBEpisode || null,
            episodeTitle: raw.episodeTitle || epMeta.title || '',
            progress: progress,
            duration: duration,
            _isContinueWatching: true,
            _raw: raw
        };
    }

    function normalizeAnime(raw) {
        if (!raw) return null;
        var media = raw.media || raw.anime || raw;
        if (isAdultMedia(media)) return null;
        var listData = raw.listData || media.listData || null;
        var episodeNumber = null;
        if (typeof raw.episodeNumber === 'number') episodeNumber = raw.episodeNumber;
        else if (listData && typeof listData.progress === 'number') episodeNumber = listData.progress + 1;

        var progress = null, duration = null;
        if (typeof raw.currentTime === 'number') progress = raw.currentTime;
        if (typeof raw.duration === 'number') duration = raw.duration;

        var updatedAt = null;
        if (typeof raw.updatedAt === 'number') updatedAt = raw.updatedAt;
        else if (typeof raw.updated_at === 'number') updatedAt = raw.updated_at;
        else if (typeof media.updatedAt === 'number') updatedAt = media.updatedAt;
        else if (typeof raw.mediaId === 'number' && typeof raw._updatedAt === 'number') updatedAt = raw._updatedAt;

        return {
            mediaId: media.id || media.mediaId || raw.mediaId,
            title: extractTitleText(media.title || raw.title),
            coverImage: extractCardImage(media.coverImage || media.image || raw.coverImage),
            posterLarge: extractImageUrl(media.coverImage || media.image || raw.coverImage),
            bannerImage: extractImageUrl(media.bannerImage) ||
                         extractImageUrl(media.coverImage || raw.coverImage),
            episodes: media.episodes || raw.episodes || null,
            format: media.format || raw.format || '',
            status: media.status || raw.status || '',
            genres: media.genres || [],
            meanScore: media.meanScore || null,
            year: media.seasonYear || (media.startDate && media.startDate.year) || null,
            episodeLength: media.duration || null,
            nextAiring: media.nextAiringEpisode || null,
            description: media.description || raw.description || '',
            episodeNumber: episodeNumber,
            progress: progress,
            duration: duration,
            listData: listData,
            _listType: raw._listType || (listData && listData.status) || '',
            updatedAt: updatedAt,
            _raw: raw
        };
    }

    function deriveContinueWatching(library) {
        if (!library || library.length === 0) return [];
        return library.filter(function (entry) {
            var status = entry._listStatus || (entry.listData && entry.listData.status) || '';
            if (status === 'CURRENT' || status === 'current') return true;
            if (entry.listData && typeof entry.listData.progress === 'number' &&
                entry.listData.progress > 0 &&
                status !== 'COMPLETED' && status !== 'DROPPED') {
                return true;
            }
            return false;
        });
    }

    // ===== API Client =====
    var api = {
        request: function (endpoint, options) {
            options = options || {};
            var url = CONFIG.serverUrl + CONFIG.apiPath + endpoint;
            var headers = {
                'Content-Type': 'application/json',
                'Accept': 'application/json',
                'X-Seanime-Client-Id': getServerClientId() || getClientId()
            };
            var clientProof = getServerClientIdProof();
            if (clientProof) headers['X-Seanime-Client-Id-Proof'] = clientProof;
            if (CONFIG.passwordHash) headers['X-Seanime-Token'] = CONFIG.passwordHash;
            if (options.headers) {
                for (var h in options.headers) headers[h] = options.headers[h];
            }

            return fetch(url, {
                method: options.method || 'GET',
                headers: headers,
                body: options.body,
                credentials: 'include'
            }).then(function (response) {
                // Capture server-issued client ID header from every response
                captureServerClientId(response);
                setConnectionStatus(true);

                if (response.status === 401 && CONFIG.passwordHash) handleSessionExpired('HTTP 401');

                if (!response.ok) {
                    // Seanime answers errors with {"error":"..."}; surface it.
                    return response.text().then(function (t) {
                        var detail = '';
                        try { detail = (JSON.parse(t) || {}).error || ''; }
                        catch (e) { detail = (t || '').slice(0, 300); }
                        throw new Error('HTTP ' + response.status + ': ' + (detail || response.statusText));
                    });
                }
                return options.text ? response.text() : response.json();
            }).catch(function (error) {
                // Probe endpoints (Queue/Profile) intentionally 404 on Seanime 3.10.3:
                // suppress inspector spam – hand off to caller via DEBUG only.
                var isProbe = options.silent404 && error && error.message && error.message.indexOf('404') >= 0;
                if (isProbe) { DEBUG && console.log('[API probe 404] ' + endpoint); }
                else { console.error('[API] ' + endpoint + ':', error); }
                if (!/^HTTP \d+/.test(error && error.message || '')) setConnectionStatus(false);   // network error
                throw error;
            });
        },

        ping: function () { return this.request('/status'); },

        getLibraryCollection: function () {
            return this.request('/library/collection').then(function (data) {
                logJSON('[API] /library/collection raw response:', data);
                var entries = extractLibraryEntries(data);
                DEBUG && console.log('[API] library entries count:', entries.length);
                var cw = extractContinueWatchingFromCollection(data);
                DEBUG && console.log('[API] continue-watching from collection:', cw.length);
                if (cw.length > 0) logJSON('[API] sample continue-watching item:', cw[0]);
                return {
                    entries: entries.map(normalizeAnime).filter(function (x) { return x && x.mediaId; }),
                    continueWatching: cw.map(normalizeContinueWatching).filter(function (x) { return x && x.mediaId; })
                };
            }).catch(function (e) {
                console.error('[API] getLibraryCollection failed:', e);
                return { entries: [], continueWatching: [] };
            });
        },

        getHomeItems: function () {
            return this.request('/status/home-items').then(function (data) {
                logJSON('[API] /status/home-items raw response:', data);
                var items = extractContinueWatchingFromHomeItems(data);
                return items.map(normalizeContinueWatching).filter(function (x) { return x && x.mediaId; });
            }).catch(function () { return []; });
        },

        // Subtitle files that sit next to a local video (same folder, same name).
        getLocalSubtitles: function (path) {
            return this.request('/mediastream/local-subtitles?path=' + encodeURIComponent(path)).then(function (data) {
                return unwrapData(data) || [];
            });
        },
        getFileText: function (path) {
            return this.request('/mediastream/file?path=' + encodeURIComponent(path), { text: true });
        },

        // Airing schedule of the anime on the user's lists.
        getSchedule: function () {
            return this.request('/library/schedule').then(function (data) {
                return unwrapData(data) || [];
            });
        },

        // Manual torrent choice.
        searchTorrents: function (body) {
            return this.request('/torrent/search', { method: 'POST', body: JSON.stringify(body) }).then(function (data) {
                return unwrapData(data) || {};
            });
        },
        getTorrentFilePreviews: function (torrent, episodeNumber, media) {
            return this.request('/torrentstream/torrent-file-previews', {
                method: 'POST',
                body: JSON.stringify({ torrent: torrent, episodeNumber: episodeNumber, media: media })
            }).then(function (data) { return unwrapData(data) || []; });
        },

        // Add / update / remove an entry on the user's AniList (score is 0-100 "raw").
        editListEntry: function (body) {
            return this.request('/anilist/list-entry', { method: 'POST', body: JSON.stringify(body) });
        },
        deleteListEntry: function (mediaId) {
            return this.request('/anilist/list-entry', {
                method: 'DELETE',
                body: JSON.stringify({ mediaId: mediaId, type: 'anime' })
            });
        },
        getMediaDetails: function (mediaId) {
            return this.request('/anilist/media-details/' + mediaId).then(function (data) {
                return unwrapData(data) || null;
            });
        },

        // Library entry: list data (status/progress/score) and episodes that exist on disk.
        getAnimeEntry: function (mediaId) {
            return this.request('/library/anime-entry/' + mediaId).then(function (data) {
                return unwrapData(data) || null;
            });
        },

        getEpisodes: function (mediaId) {
            return this.request('/anime/episode-collection/' + mediaId).then(function (data) {
                logJSON('[API] episodes response for ' + mediaId + ':', data);
                var d = unwrapData(data);
                if (Array.isArray(d)) return d;
                if (d && Array.isArray(d.episodes)) return d.episodes;
                if (d && Array.isArray(d.items)) return d.items;
                if (d && Array.isArray(d.list)) return d.list;
                return [];
            }).catch(function (e) {
                console.warn('[API] getEpisodes failed:', e);
                return [];
            });
        },

        startTorrentStream: function (mediaId, episodeNumber, aniDbEpisode, manual) {
            var body = {
                mediaId: mediaId,
                episodeNumber: episodeNumber,
                playbackType: 'externalPlayerLink',
                clientId: getServerClientId() || getClientId(),
                autoSelect: true
            };
            if (aniDbEpisode) body.aniDbEpisode = aniDbEpisode;
            if (manual && manual.torrent) {
                body.autoSelect = false;
                body.torrent = manual.torrent;
                if (manual.fileIndex != null) body.fileIndex = manual.fileIndex;
            }
            DEBUG && console.log('[TorrentStream] POST /start', manual && manual.torrent ? { manual: manual.torrent.name } : body);
            return this.request('/torrentstream/start', {
                method: 'POST',
                body: JSON.stringify(body)
            }).then(function (data) {
                logJSON('[TorrentStream] start response:', data);
                return true;
            });
        },

        stopTorrentStream: function () {
            var body = { clientId: getServerClientId() || getClientId() };
            if (state.activeSessionId) body.sessionId = state.activeSessionId;
            return this.request('/torrentstream/stop', {
                method: 'POST',
                body: JSON.stringify(body)
            }).then(function () {
                state.activeSessionId = null;
            }).catch(function (e) {
                console.warn('[TorrentStream] stop failed (non-fatal):', e);
                state.activeSessionId = null;
            });
        },

        // POST /anilist/list-anime is what Seanime's own search/discover use.
        // page and perPage must both be sent or the server rejects the call.
        // isAdult:false is always sent; ecchi is removed client-side (isAdultMedia).
        listAnime: function (extra) {
            var body = { page: 1, perPage: 40, isAdult: false };
            for (var k in extra) body[k] = extra[k];
            return this.request('/anilist/list-anime', {
                method: 'POST',
                body: JSON.stringify(body)
            }).then(function (data) {
                var d = unwrapData(data);
                var page = d && (d.Page || d.page);
                return (page && (page.media || page.Media)) || [];
            });
        },

        search: function (query) {
            return this.listAnime({ search: query, perPage: 30 });
        },

        // The user's full AniList anime collection (all statuses).
        getAnimeCollection: function () {
            return this.request('/anilist/collection').then(function (data) {
                var d = unwrapData(data);
                var mlc = d && (d.MediaListCollection || d.mediaListCollection);
                return (mlc && mlc.lists) || [];
            });
        },

        // Marks an episode as watched on AniList. Seanime does not track
        // torrent-stream playback itself, so the client has to do this.
        updateEntryProgress: function (mediaId, episodeNumber, totalEpisodes) {
            return this.request('/library/anime-entry/update-progress', {
                method: 'POST',
                body: JSON.stringify({
                    mediaId: mediaId,
                    episodeNumber: episodeNumber,
                    totalEpisodes: totalEpisodes || 0
                })
            });
        },

        // Resume position (Seanime "watch continuity"). Resolves null when
        // nothing is saved or continuity is disabled on the server.
        getContinuityItem: function (mediaId) {
            return this.request('/continuity/item/' + mediaId).then(function (data) {
                var d = unwrapData(data);
                return (d && d.found && d.item) ? d.item : null;
            }).catch(function () { return null; });
        },

        saveContinuity: function (opts) {
            return this.request('/continuity/item', {
                method: 'PATCH',
                body: JSON.stringify({ options: opts })
            }).catch(function (e) { console.warn('[Continuity] save failed (non-fatal):', e); });
        },
        // P0 – Queue + Profile (Seanime 3.10.3 has NO such routes – stubs only, no 404 spam)
        getActiveTorrents: function () {
            DEBUG && console.log('[API] getActiveTorrents: no server route (Seanime 3.10.3) → []');
            return Promise.resolve([]);
        },
        getQueue: function () { return this.getActiveTorrents(); },
        getViewer: function () {
            DEBUG && console.log('[API] getViewer: no server route (Seanime 3.10.3) → null');
            return Promise.resolve(null);
        }
    };

    // ===== Session =====
    function isSetupComplete() { return credGet(STORAGE_KEYS.SETUP_COMPLETE) === '1'; }
    function markSetupComplete() { credSet(STORAGE_KEYS.SETUP_COMPLETE, '1'); }
    function clearSession() {
        credRemove(STORAGE_KEYS.SETUP_COMPLETE);
        credRemove(STORAGE_KEYS.PASSWORD_HASH);
        try { localStorage.removeItem(STORAGE_KEYS.SERVER_PASSWORD); } catch (e) {}
        localStorage.removeItem(STORAGE_KEYS.SERVER_CLIENT_ID);
        localStorage.removeItem(STORAGE_KEYS.SERVER_CLIENT_ID_PROOF);
    }
    // Re-saves the login in the store chosen by the "Stay signed in" setting.
    function persistCredentials() {
        if (!isSetupComplete() && !CONFIG.serverUrl) return;
        credSet(STORAGE_KEYS.PASSWORD_HASH, CONFIG.passwordHash || '');
        credSet(STORAGE_KEYS.SETUP_COMPLETE, '1');
    }

    // "192.168.1.5:43211" -> "http://192.168.1.5:43211"; trims spaces, query and trailing slashes.
    function normalizeServerUrl(input) {
        var u = String(input || '').replace(/^\s+|\s+$/g, '');
        if (!u) return '';
        if (!/^[a-z][a-z0-9+.\-]*:\/\//i.test(u)) u = 'http://' + u;
        u = u.replace(/[?#].*$/, '').replace(/\/+$/, '');
        return u.replace(/^(https?):/i, function (m, scheme) { return scheme.toLowerCase() + ':'; });
    }

    function describeNetworkFailure(url) {
        if (/^https:/i.test(url)) {
            return 'Could not open a secure connection to ' + url + '. If the server uses a self-signed ' +
                   'certificate the TV will reject it \u2014 use a certificate from a trusted authority ' +
                   '(for example behind a reverse proxy with Let\u2019s Encrypt), or connect with http:// on your home network.';
        }
        return 'Could not reach server at ' + url;
    }

    // existingHash: reuse a saved login instead of a typed password
    function login(url, password, existingHash) {
        state.loggingIn = true;
        state.signingOut = false;
        CONFIG.serverUrl = normalizeServerUrl(url);
        CONFIG.passwordHash = existingHash != null ? existingHash : (password ? sha256(password) : '');
        localStorage.setItem(STORAGE_KEYS.SERVER_URL, CONFIG.serverUrl);

        DEBUG && console.log('[Login] Hash:', CONFIG.passwordHash.slice(0, 16) + (CONFIG.passwordHash ? '\u2026' : '(no password)'));

        return api.ping().then(function () {
            return api.request('/library/collection');
        }).then(function () {
            markSetupComplete();
            persistCredentials();
            setConnectionStatus(true);
            DEBUG && console.log('[Login] Server client ID:', getServerClientId() || '(none captured)');
            state.loggingIn = false;
            startSession();
            return true;
        }).catch(function (e) {
            state.loggingIn = false;
            setConnectionStatus(false);
            var msg = (e && e.message) || '';
            if (msg.indexOf('401') >= 0 || msg.indexOf('403') >= 0) {
                throw new Error('Authentication failed. Check the server password.');
            }
            if (msg.indexOf('Failed to fetch') >= 0 || msg.indexOf('NetworkError') >= 0 || e instanceof TypeError) {
                throw new Error(describeNetworkFailure(CONFIG.serverUrl));
            }
            throw e;
        });
    }

    // Keeps the live connection and health check running while signed in.
    function startSession() {
        startSocketLoop();
        startHealthCheck();
    }

    function logout() {
        DEBUG && console.log('[Session] Logout');
        stopPlayback();
        stopHeroRotation();
        stopSocketLoop();
        stopHealthCheck();
        clearSession();
        CONFIG.passwordHash = '';
        setConnectionStatus(false);
        openSetupScreen();
    }

    // ===== Home / Discover / Schedule: D-pad navigation across rows =====
    // Cards only reacted to OK before; nothing moved focus between cards or rows.
    // Rows = the hero button (a row of one) plus every visible .card-row, in DOM order.
    function homeNavRows() {
        var area = state.view === 'discover' ? $('#discover-area')
                 : state.view === 'schedule' ? $('#schedule-area')
                 : state.view === 'queue' ? $('#queue-area')
                 : state.view === 'profile' ? $('#profile-area')
                 : $('#content-area');
        var rows = [];
        if (!area) return rows;
        // Discover filters + all rows. Filters are first so UP from first Discover card lands on them.
        if (state.view === 'discover') {
            var df = area.querySelectorAll('#discover-filters .df-chip');
            if (df && df.length) {
                var fRow = [];
                for (var fi = 0; fi < df.length; fi++) fRow.push(df[fi]);
                rows.push(fRow);
            }
        }
        var nodes = area.querySelectorAll('#hero-play-btn, .card-row, .cast-row, #queue-rows, #profile-card, #profile-stats, #profile-bar, #profile-health, #profile-activity, #profile-cw, #profile-prefs, #profile-actions');
        for (var i = 0; i < nodes.length; i++) {
            var n = nodes[i], items = [];
            if (n.id === 'hero-play-btn') {
                if (n.style.display === 'none') continue;
                items.push(n);
            } else if (n.id === 'queue-rows') {
                for (var j = 0; j < n.children.length; j++) {
                    if (n.children[j].classList.contains('queue-item')) items.push(n.children[j]);
                }
            } else if (n.id === 'profile-card' || n.id === 'profile-stats' || n.id === 'profile-bar' || n.id === 'profile-health' || n.id === 'profile-prefs' || n.id === 'profile-actions') {
                if (n.children.length) {
                    for (var k = 0; k < n.children.length; k++) {
                        var c = n.children[k];
                        if (c.tabIndex >= 0 || c.querySelector('[tabindex]')) {
                            var focusable = c.tabIndex >= 0 ? c : c.querySelector('[tabindex]');
                            if (focusable) items.push(focusable);
                        }
                    }
                    if (!items.length && n.offsetWidth) {
                        // profile sections that are focusable as a whole (health/prefs)
                        if (n.tabIndex >= 0) items.push(n);
                        else if (n.offsetWidth) items.push(n);
                    }
                } else if (n.tabIndex >= 0) {
                    items.push(n);
                }
            } else if (n.classList.contains('cast-row')) {
                for (var j = 0; j < n.children.length; j++) {
                    if (n.children[j].classList.contains('cast-card')) items.push(n.children[j]);
                }
            } else {
                for (var j = 0; j < n.children.length; j++) {
                    if (n.children[j].classList.contains('anime-card')) items.push(n.children[j]);
                }
            }
            if (!items.length) continue;
            if (!n.offsetHeight && !n.offsetWidth) continue;   // hidden section
            rows.push(items);
        }
        return rows;
    }

    function closestInRow(items, fromEl) {
        var fr = fromEl.getBoundingClientRect();
        var fx = fr.left + fr.width / 2, best = items[0], bestD = Infinity;
        for (var i = 0; i < items.length; i++) {
            var r = items[i].getBoundingClientRect();
            var d = Math.abs(r.left + r.width / 2 - fx);
            if (d < bestD) { bestD = d; best = items[i]; }
        }
        return best;
    }

    function handleHomeKeys(keyCode, e) {
        var K = KEY_CODES;
        if (keyCode !== K.UP && keyCode !== K.DOWN && keyCode !== K.LEFT && keyCode !== K.RIGHT) return false;
        var active = document.activeElement;
        var header = $('#main-header');
        // header buttons and the search box have their own handlers
        if (!active || active.tagName === 'INPUT' || (header && header.contains(active))) return false;

        // LEFT/RIGHT along a row (the key that gets held down) needs only the neighbouring card.
        // The general code below scans every card on the page and forces a layout per row.
        // Extended to anime-card + cast-card + queue-item (Bug 1).
        var activeCls = active.classList.contains('anime-card') ? 'anime-card'
                      : active.classList.contains('cast-card') ? 'cast-card'
                      : active.classList.contains('queue-item') ? 'queue-item'
                      : active.classList.contains('df-chip') ? 'df-chip'
                      : active.classList.contains('profile-action') ? 'profile-action'
                      : active.classList.contains('profile-activity-row') ? 'profile-activity-row' : null;
        var activeInRow = activeCls && active.parentNode &&
                         (active.parentNode.classList.contains('card-row') ||
                          active.parentNode.id === 'discover-filters' ||
                          active.parentNode.id === 'profile-activity' ||
                          active.parentNode.id === 'profile-cw' ||
                          active.parentNode.id === 'profile-actions' ||
                          active.parentNode.classList.contains('cast-row') ||
                          active.parentNode.id === 'queue-rows');
        if ((keyCode === K.LEFT || keyCode === K.RIGHT) && activeCls && activeInRow) {
            e.preventDefault();
            var stepH = keyCode === K.RIGHT ? 'nextElementSibling' : 'previousElementSibling';
            var sibH = active[stepH];
            while (sibH && !sibH.classList.contains(activeCls)) sibH = sibH[stepH];
            if (sibH) sibH.focus();
            return true;
        }

        var rows = homeNavRows(), r = -1, c = -1;
        for (var i = 0; i < rows.length && r < 0; i++) {
            var idx = rows[i].indexOf(active);
            if (idx >= 0) { r = i; c = idx; }
        }
        if (r < 0) {                       // focus is nowhere useful: enter the first row
            if (!rows.length) return false;
            e.preventDefault();
            rows[0][0].focus();
            return true;
        }
        e.preventDefault();

        if (keyCode === K.LEFT || keyCode === K.RIGHT) {
            var nc = c + (keyCode === K.RIGHT ? 1 : -1);
            if (nc >= 0 && nc < rows[r].length) rows[r][nc].focus();
            return true;
        }

        // Detect UP from the "Recently Added" row (index 1 when hero is row 0) and go to hero instead of header
        var nr = r + (keyCode === K.DOWN ? 1 : -1);
        if (nr < 0) {                      // above the first row -> header tab of the current view
            // Home: the row below header is the hero. If we're on the first card-row (Recently Added) and
            // the hero exists, go to hero rather than straight to header.
            if (state.view === 'home' && r === 1) {
                var hero = $('#hero-play-btn');
                if (hero && hero.style.display !== 'none' && hero.offsetWidth) {
                    hero.focus();
                    if (hero.scrollIntoView) { try { hero.scrollIntoView({ block: 'nearest' }); } catch (e3) {} }
                    return true;
                }
            }
            var tab = $(state.view === 'discover' ? '#nav-discover' :
                        state.view === 'schedule' ? '#nav-schedule' :
                        state.view === 'queue' ? '#nav-queue' :
                        state.view === 'profile' ? '#nav-profile' : '#nav-home');
            if (tab) tab.focus();
            var area = state.view === 'discover' ? $('#discover-area') :
                       state.view === 'schedule' ? $('#schedule-area') : $('#content-area');
            if (area) area.scrollTop = 0;
            return true;
        }
        if (nr >= rows.length) return true;
        var target = closestInRow(rows[nr], active);
        target.focus();
        if (target.id === 'hero-play-btn') $('#content-area').scrollTop = 0;
        // keep the row's container scrolled into view (queue/profile have no hero)
        var container = target && target.parentNode;
        if (container && container.scrollIntoView) {
            try { container.scrollIntoView({ block: 'nearest' }); } catch (e2) {}
        }
        return true;
    }

    // ===== Key Handling =====
    function handleKeyDown(e) {
        var keyCode = e.keyCode;
        if (state.picker) { handlePickerKeys(keyCode, e); return; }
        if (state.currentScreen === 'setup') return;
        if (state.currentScreen === 'player') { handlePlayerKeys(keyCode, e); return; }
        if (state.currentScreen === 'settings') { handleSettingsKeys(keyCode, e); return; }

        if (state.currentScreen === 'detail' && handleDetailKeys(keyCode, e)) return;
        if (state.currentScreen === 'home' && handleHomeKeys(keyCode, e)) return;

        if (keyCode === KEY_CODES.BLUE &&
            (state.currentScreen === 'home' || state.currentScreen === 'detail')) {
            e.preventDefault(); logout(); return;
        }
        if (keyCode === KEY_CODES.RETURN && state.currentScreen === 'detail') {
            if (state.detailStack.length) { openAnimeDetail(state.detailStack.pop(), true); return; }
            showScreen('home');
            var back = state.lastCard;
            if (back && document.body.contains(back)) { try { back.focus(); } catch (err) {} }
        }
    }

    function handlePlayerKeys(keyCode, e) {
        var K = KEY_CODES;
        var prevent = function () { if (e && e.preventDefault) e.preventDefault(); };
        var exit = function () { stopPlayback(); hidePlayerError(); leavePlayer(); };
        var loading = !$('#torrent-loading').classList.contains('hidden');

        // Error dialog: arrows switch between the buttons, OK presses, BACK leaves
        if (state.playerError) {
            var btns = ['#player-error-retry', '#player-error-pick', '#player-error-back'].map(function (id) { return $(id); })
                .filter(function (b) { return b && b.style.display !== 'none'; });
            var at = btns.indexOf(document.activeElement);
            if (keyCode === K.ENTER) { prevent(); if (btns[at]) btns[at].click(); }
            else if (keyCode === K.RETURN || keyCode === K.STOP) { exit(); }
            else if (keyCode === K.LEFT || keyCode === K.UP) { prevent(); btns[(at <= 0 ? btns.length : at) - 1].focus(); }
            else if (keyCode === K.RIGHT || keyCode === K.DOWN) { prevent(); btns[(at + 1) % btns.length].focus(); }
            return;
        }

        // "Up next" countdown: OK = play now, BACK/STOP/DOWN = cancel
        if (state.upNext) {
            if (keyCode === K.ENTER) { prevent(); playRelativeEpisode(1); }
            else if (keyCode === K.RETURN || keyCode === K.STOP || keyCode === K.DOWN) { prevent(); exit(); }
            return;
        }

        // Audio / subtitle picker: UP/DOWN move, OK applies, BACK/LEFT closes
        if (state.trackPanelKind) {
            if (keyCode === K.UP) { prevent(); moveTrackFocus(-1); return; }
            if (keyCode === K.DOWN) { prevent(); moveTrackFocus(1); return; }
            if (keyCode === K.ENTER) {
                prevent();
                var cur = document.activeElement;
                if (cur && cur.classList && cur.classList.contains('track-item')) cur.click();
                return;
            }
            if (keyCode === K.RETURN || keyCode === K.LEFT) { prevent(); closeTrackPanel(); return; }
            if (keyCode === K.RIGHT) { prevent(); return; }
        }

        // BACK while scrubbing only cancels the scrub; it does not leave the player
        if (keyCode === K.RETURN && state.scrub) { prevent(); cancelScrub(false); return; }
        if (keyCode === K.RETURN || keyCode === K.STOP) { exit(); return; }
        if (loading) return;

        if (keyCode === K.PLAY) { avplayPlay(); return; }
        if (keyCode === K.PAUSE) { avplayPause(); return; }
        // The remote's REWIND / FORWARD scrub too, so holding them accelerates
        if (keyCode === K.REWIND) { prevent(); scrubStep(-1); return; }
        if (keyCode === K.FORWARD) { prevent(); scrubStep(1); return; }

        if (controlsShown()) {
            // OSD visible. Focus moves: buttons <-> progress bar <-> Skip button (UP / DOWN).
            // On the bar LEFT/RIGHT scrub; elsewhere they move between the buttons.
            var active = document.activeElement;
            var bar = $('#progress-bar'), skip = $('#skip-btn');
            var onBar = !!bar && active === bar;
            var onSkip = !!skip && active === skip && !!state.skipShown;
            switch (keyCode) {
                case K.LEFT:
                    prevent();
                    if (onBar) scrubStep(-1); else if (!onSkip) moveCtrlFocus(-1);
                    showControls();
                    break;
                case K.RIGHT:
                    prevent();
                    if (onBar) scrubStep(1); else if (!onSkip) moveCtrlFocus(1);
                    showControls();
                    break;
                case K.ENTER:
                    prevent();
                    if (onBar && state.scrub) commitScrub();
                    else if (onSkip) skipNow();
                    else if (active && active.classList && active.classList.contains('ctrl-btn')) active.click();
                    else togglePlayPause();
                    showControls();
                    break;
                case K.UP:
                    prevent();
                    if (state.scrub) commitScrub();
                    if (onBar) { if (state.skipShown && skip) { try { skip.focus(); } catch (err) {} } }
                    else if (!onSkip && bar) { try { bar.focus(); } catch (err) {} }
                    showControls();
                    break;
                case K.DOWN:
                    prevent();
                    if (state.scrub) commitScrub();
                    if (onSkip && bar) { try { bar.focus(); } catch (err) {} showControls(); }
                    else if (onBar) { var pp = $('#ctrl-play-pause'); if (pp) { try { pp.focus(); } catch (err) {} } showControls(); }
                    else hideControls();
                    break;
            }
        } else {
            // OSD hidden: LEFT/RIGHT start scrubbing (OSD appears), OK skips an intro/outro when the
            // Skip button is up (otherwise it brings the OSD up), UP/DOWN bring the OSD up
            switch (keyCode) {
                case K.LEFT:  prevent(); scrubStep(-1); break;
                case K.RIGHT: prevent(); scrubStep(1); break;
                case K.ENTER: prevent(); if (state.skipShown) skipNow(); else showControls(); break;
                case K.UP:
                case K.DOWN:  prevent(); showControls(); break;
            }
        }
    }

    // ===== Hero Carousel =====
    function renderHeroCarousel(items) {
        heroState.items = items || [];
        heroState.currentIndex = 0;
        if (heroState.items.length === 0) {
            $('#hero-title').textContent = 'Nothing to Continue';
            $('#hero-meta').textContent = 'Start watching something from your library below.';
            $('#hero-backdrop')._bgTok = ($('#hero-backdrop')._bgTok || 0) + 1;
            $('#hero-backdrop').style.backgroundImage = 'none';
            $('#hero-backdrop').style.opacity = '1';
            $('#hero-progress-bar').style.width = '0%';
            $('#hero-play-btn').style.display = 'none';
            $('#hero-dots').innerHTML = '';
            return;
        }
        $('#hero-play-btn').style.display = 'inline-block';
        buildHeroDots();
        showHeroSlide(0);
        startHeroRotation();

        var playBtn = $('#hero-play-btn');
        playBtn.onclick = function () {
            var current = heroState.items[heroState.currentIndex];
            if (current) playFromHero(current);
        };
        playBtn.onkeydown = function (e) {
            if (e.keyCode === KEY_CODES.LEFT) { e.preventDefault(); prevHeroSlide(); }
            else if (e.keyCode === KEY_CODES.RIGHT) { e.preventDefault(); nextHeroSlide(); }
            else if (e.keyCode === KEY_CODES.ENTER) {
                e.preventDefault();
                var current = heroState.items[heroState.currentIndex];
                if (current) playFromHero(current);
            }
        };
        playBtn.onfocus = stopHeroRotation;
        playBtn.onblur = function () { if (state.currentScreen === 'home') startHeroRotation(); };
    }

    function buildHeroDots() {
        var dotsEl = $('#hero-dots');
        dotsEl.innerHTML = '';
        for (var i = 0; i < heroState.items.length; i++) {
            var dot = document.createElement('div');
            dot.className = 'hero-dot' + (i === 0 ? ' active' : '');
            dotsEl.appendChild(dot);
        }
    }

    function showHeroSlide(index) {
        var item = heroState.items[index];
        if (!item) return;
        heroState.currentIndex = index;
        var backdrop = $('#hero-backdrop');
        var heroT0 = Date.now();
        backdrop.style.opacity = '0';
        setBackdrop(backdrop, [item.bannerImage, item.coverImage], function () {
            // let the fade-out play, then fade the new image in (only if this slide is still current)
            setTimeout(function () {
                if (heroState.currentIndex === index) backdrop.style.opacity = '1';
            }, Math.max(0, 150 - (Date.now() - heroT0)));
        });
        $('#hero-title').textContent = item.title || 'Unknown';
        var percent = 0;
        if (item.progress && item.duration && item.duration > 0) {
            percent = Math.min(100, (item.progress / item.duration) * 100);
        }
        $('#hero-progress-bar').style.width = percent + '%';
        var metaParts = [];
        if (item.episodeNumber) metaParts.push('Episode ' + item.episodeNumber);
        if (item.format) metaParts.push(item.format);
        if (percent > 0) metaParts.push(Math.round(percent) + '% watched');
        $('#hero-meta').textContent = metaParts.join(' • ');
        var dots = $('#hero-dots').children;
        for (var i = 0; i < dots.length; i++) {
            if (i === index) dots[i].classList.add('active');
            else dots[i].classList.remove('active');
        }
    }

    function nextHeroSlide() {
        if (heroState.items.length === 0) return;
        showHeroSlide((heroState.currentIndex + 1) % heroState.items.length);
        startHeroRotation();
    }
    function prevHeroSlide() {
        if (heroState.items.length === 0) return;
        showHeroSlide((heroState.currentIndex - 1 + heroState.items.length) % heroState.items.length);
        startHeroRotation();
    }
    function startHeroRotation() {
        stopHeroRotation();
        if (heroState.items.length <= 1) return;
        heroState.rotationTimer = setInterval(function () {
            // Do not swap (and re-download) banners nobody can see: another screen or view is
            // open (the player included: it competes with the stream for bandwidth), or the
            // hero is scrolled out of view.
            if (state.currentScreen !== 'home' || state.view !== 'home') return;
            var area = $('#content-area');
            if (area && area.scrollTop > 380) return;
            showHeroSlide((heroState.currentIndex + 1) % heroState.items.length);
        }, 8000);
    }
    function stopHeroRotation() {
        if (heroState.rotationTimer) { clearInterval(heroState.rotationTimer); heroState.rotationTimer = null; }
    }
    function playFromHero(item) {
        state.currentAnime = item;
        state.playbackOrigin = 'home';
        var raw = item._raw || {};
        playEpisodeAuto(item, item.episodeNumber || 1,
            { aniDBEpisode: item.aniDbEpisode || null, localFile: raw.localFile || null });
    }

    // ===== Image loading =====
    // Why the old loader was unreliable: an IntersectionObserver only widens the
    // *viewport*, not the clip of scrolling ancestors (#content-area and every
    // horizontal .card-row), so posters outside the visible part of a row were never
    // loaded ahead of time and popped in late (or not at all while smooth-scrolling).
    // A single failed request also left the "No Image" placeholder forever, and the
    // observer swapped images for a 1x1 gif whenever their screen was hidden.
    //
    // This loader works from real geometry instead:
    //   * images near the screen are queued, nearest first, max IMG_MAX_PARALLEL at a time
    //   * a failed or hanging request is retried, then the next candidate URL is tried
    //   * images far from the screen release their bitmap (Tizen 4.0 has little RAM)
    //   * images inside hidden screens/views are left alone (no reload when coming back)
    var TRANSPARENT_GIF = 'data:image/gif;base64,R0lGODlhAQABAIAAAAAAAP///yH5BAEAAAAALAAAAAABAAEAAAIBRAA7';
    var IMG_MAX_PARALLEL = 6;
    var IMG_MAX_TRIES = 3;              // attempts per URL
    var IMG_TIMEOUT_MS = 15000;         // a request with no answer counts as failed
    var IMG_RETRY_AFTER_MS = 12000;     // a permanently failed image is tried again while visible
    var IMG_MAX_ROUNDS = 3;
    var IMG_LOAD_X = 1200, IMG_LOAD_Y = 900;    // start loading this close to the screen edge
    var IMG_KEEP_X = 2400, IMG_KEEP_Y = 1800;   // release the bitmap beyond this (decoded posters are RAM)
    var IMG_IDLE = 0, IMG_LOADING = 1, IMG_LOADED = 2, IMG_FAILED = 3, IMG_WAITING = 4;
    var imgRegistry = [];
    var imgActive = 0;
    var imgTimer = null;
    var imgInited = false;
    var imgPending = [];            // sorted candidates from the last scan: next to download
    var imgTimerDue = 0;

    // Coalesces requests: one scan runs at the earliest requested time. A burst of
    // scroll/focus events (D-pad held down) therefore costs one scan, not one per event.
    function imgSchedule(delay) {
        var d = delay == null ? 80 : delay, due = Date.now() + d;
        if (imgTimer) {
            if (due >= imgTimerDue) return;
            clearTimeout(imgTimer);
        }
        imgTimerDue = due;
        imgTimer = setTimeout(imgRefresh, d);
    }

    function imgInit() {
        if (imgInited) return;
        imgInited = true;
        var kick = function () { imgSchedule(200); };
        document.addEventListener('scroll', kick, true);   // scroll does not bubble: capture it
        document.addEventListener('focus', kick, true);
        window.addEventListener('resize', kick);
        window.addEventListener('online', function () {
            for (var i = 0; i < imgRegistry.length; i++) {
                var lz = imgRegistry[i]._lz;
                if (lz && lz.state === IMG_FAILED) lz.failedAt = 0;
            }
            imgSchedule(0);
        });
        // safety net: covers view switches, late layout and anything that fires no event
        setInterval(function () {
            if (!document.hidden && state.currentScreen !== 'player') imgSchedule(0);
        }, 4000);
    }

    function imgClearTimers(lz) {
        if (lz.timer) { clearTimeout(lz.timer); lz.timer = null; }
        if (lz.retryTimer) { clearTimeout(lz.retryTimer); lz.retryTimer = null; }
    }

    function imgAbort(img) {
        var lz = img._lz;
        if (!lz) return;
        imgClearTimers(lz);
        if (lz.state === IMG_LOADING) imgActive = Math.max(0, imgActive - 1);
        lz.state = IMG_IDLE;
    }

    function imgUnload(img) {
        var lz = img._lz;
        imgAbort(img);
        lz.cur = TRANSPARENT_GIF;
        img.src = TRANSPARENT_GIF;
    }

    function imgStart(img) {
        var lz = img._lz;
        lz.state = IMG_LOADING;
        lz.tries++;
        lz.cur = lz.urls[lz.idx];
        imgActive++;
        lz.timer = setTimeout(function () { lz.timer = null; imgFail(img); }, IMG_TIMEOUT_MS);
        img.src = lz.cur;
    }

    function imgFail(img) {
        var lz = img._lz;
        if (!lz || lz.state !== IMG_LOADING) return;
        imgClearTimers(lz);
        imgActive = Math.max(0, imgActive - 1);
        if (lz.tries < IMG_MAX_TRIES) {
            lz.state = IMG_WAITING;
            lz.retryTimer = setTimeout(function () {
                lz.retryTimer = null;
                lz.state = IMG_IDLE;
                imgSchedule(0);
            }, 700 * lz.tries);
        } else if (lz.idx < lz.urls.length - 1) {
            lz.idx++; lz.tries = 0; lz.state = IMG_IDLE;
        } else {
            lz.state = IMG_FAILED;
            lz.failedAt = Date.now();
            lz.cur = CONFIG.defaultImage;
            img.src = CONFIG.defaultImage;
        }
        if (lz.state === IMG_IDLE) imgPending.unshift(img);     // next candidate URL: try it right away
        imgSlotFreed();
    }

    // Start queued images while download slots are free. Uses the queue from the last scan, so it
    // reads no layout (the old code re-measured every poster each time one image finished).
    function imgPump() {
        while (imgActive < IMG_MAX_PARALLEL && imgPending.length) {
            var img = imgPending.shift(), lz = img._lz;
            if (lz && lz.state === IMG_IDLE && document.documentElement.contains(img)) imgStart(img);
        }
    }
    function imgSlotFreed() {
        imgPump();
        imgSchedule(400);               // full re-scan a little later, in case the queue went stale
    }

    function imgOnLoad() {
        var lz = this._lz;
        if (!lz || lz.state !== IMG_LOADING || this.getAttribute('src') !== lz.cur) return;
        imgClearTimers(lz);
        imgActive = Math.max(0, imgActive - 1);
        lz.state = IMG_LOADED;
        imgSlotFreed();                 // a slot is free: start the next one
    }

    function imgOnError() {
        var lz = this._lz;
        if (!lz || lz.state !== IMG_LOADING || this.getAttribute('src') !== lz.cur) return;
        imgFail(this);
    }

    function imgRefresh() {
        imgTimer = null;
        if (state.currentScreen === 'player') return;       // nothing to load behind the video
        var vw = window.innerWidth || 1920, vh = window.innerHeight || 1080;
        var queue = [], unload = [], now = Date.now();
        // Phase 1 only READS geometry (a single layout pass); phase 2 changes images.
        // Mixing the two forced a fresh layout for every poster.
        for (var i = imgRegistry.length - 1; i >= 0; i--) {
            var img = imgRegistry[i], lz = img._lz;
            if (!lz) { imgRegistry.splice(i, 1); continue; }
            if (!document.documentElement.contains(img)) {
                // not in the page (yet): forget it only if it stays detached for a while
                if (++lz.misses >= 4) {
                    imgAbort(img);
                    img.removeEventListener('load', imgOnLoad);
                    img.removeEventListener('error', imgOnError);
                    img._lz = null;
                    imgRegistry.splice(i, 1);
                }
                continue;
            }
            lz.misses = 0;
            var r = img.getBoundingClientRect();
            if (!r.width && !r.height) continue;            // inside a hidden screen / view: leave as is
            var dx = r.right < 0 ? -r.right : (r.left > vw ? r.left - vw : 0);
            var dy = r.bottom < 0 ? -r.bottom : (r.top > vh ? r.top - vh : 0);
            var near = dx <= IMG_LOAD_X && dy <= IMG_LOAD_Y;
            var far = dx > IMG_KEEP_X || dy > IMG_KEEP_Y;

            if (lz.state === IMG_IDLE) {
                if (near) queue.push({ img: img, d: dy * 3 + dx, i: i });
            } else if (lz.state === IMG_FAILED) {
                if (near && lz.rounds < IMG_MAX_ROUNDS && now - lz.failedAt > IMG_RETRY_AFTER_MS) {
                    lz.rounds++; lz.idx = 0; lz.tries = 0; lz.state = IMG_IDLE;
                    queue.push({ img: img, d: dy * 3 + dx, i: i });
                }
            } else if (far) {
                unload.push(img);                           // loaded / loading / waiting: free it
            }
        }
        for (var u = 0; u < unload.length; u++) imgUnload(unload[u]);
        queue.sort(function (a, b) { return (a.d - b.d) || (a.i - b.i); });   // nearest first, then creation (= reading) order
        imgPending = [];
        for (var q = 0; q < queue.length; q++) imgPending.push(queue[q].img);
        imgPump();
    }

    // src may be one URL or a list of fallbacks tried in order (e.g. [large, medium]).
    // Safe to call again on the same <img> (the detail poster is reused): it starts over.
    function lazyImage(img, src) {
        imgInit();
        var list = Array.isArray(src) ? src : [src], urls = [];
        for (var i = 0; i < list.length; i++) {
            if (list[i] && urls.indexOf(list[i]) < 0) urls.push(list[i]);
        }
        if (!urls.length) urls.push(CONFIG.defaultImage);

        var lz = img._lz;
        if (lz) {
            imgAbort(img);
        } else {
            lz = img._lz = {};
            imgRegistry.push(img);
            img.addEventListener('load', imgOnLoad);
            img.addEventListener('error', imgOnError);
        }
        lz.urls = urls; lz.idx = 0; lz.tries = 0; lz.rounds = 0;
        lz.state = IMG_IDLE; lz.failedAt = 0; lz.misses = 0;
        lz.timer = null; lz.retryTimer = null;
        lz.cur = TRANSPARENT_GIF;
        img.src = TRANSPARENT_GIF;
        imgSchedule(0);
    }

    // Full-screen backdrops (hero, detail): preload off-screen, then swap in, so a slow or
    // failed image never leaves a blank/stale backdrop. A newer call cancels an older one.
    function cssUrl(u) {
        return 'url("' + String(u).replace(/["\\\r\n]/g, function (c) {
            return '%' + c.charCodeAt(0).toString(16);
        }) + '")';
    }

    function setBackdrop(el, urls, done) {
        var list = [];
        (urls || []).forEach(function (u) { if (u && list.indexOf(u) < 0) list.push(u); });
        var tok = el._bgTok = (el._bgTok || 0) + 1;
        var i = 0, tries = 0;

        function finish(u) {
            if (tok !== el._bgTok) return;
            el.style.backgroundImage = u ? cssUrl(u) : 'none';
            if (done) done();
        }
        function next() {
            if (tok !== el._bgTok) return;
            if (i >= list.length) { finish(null); return; }
            var u = list[i], im = new Image(), over = false, t = null;
            var end = function (ok) {
                if (over) return;
                over = true;
                clearTimeout(t);
                im.onload = im.onerror = null;
                if (tok !== el._bgTok) return;
                if (ok) { finish(u); return; }
                if (++tries < 2) { setTimeout(next, 600); }
                else { i++; tries = 0; next(); }
            };
            im.onload = function () { end(true); };
            im.onerror = function () { end(false); };
            t = setTimeout(function () { end(false); }, 12000);
            im.src = u;
        }
        next();
    }

    // ===== Card Rendering =====
    function renderAnimeCard(anime) {
        var card = document.createElement('div');
        card.className = 'anime-card';
        card.tabIndex = 0;
        var img = document.createElement('img');
        img.alt = anime.title;
        lazyImage(img, anime.coverImage);
        var info = document.createElement('div');
        info.className = 'card-info';
        var title = document.createElement('div');
        title.className = 'card-title';
        title.textContent = anime.title;
        var meta = document.createElement('div');
        meta.className = 'card-meta';
        var metaParts = [];
        if (anime.episodes) metaParts.push(anime.episodes + ' eps');
        if (anime.format) metaParts.push(anime.format);
        meta.textContent = metaParts.join(' • ');
        info.appendChild(title); info.appendChild(meta);
        card.appendChild(img); card.appendChild(info);
        card.addEventListener('click', function () { state.lastCard = card; openAnimeDetail(anime); });
        card.addEventListener('keydown', function (e) {
            if (e.keyCode === KEY_CODES.ENTER) { e.preventDefault(); state.lastCard = card; openAnimeDetail(anime); }
        });
        return card;
    }

    // ===== Profile helpers =====
    var PROFILE_STATUS = ['CURRENT','PLANNING','COMPLETED','PAUSED','DROPPED','REPEATING'];
    var PROFILE_STATUS_COLORS = { CURRENT:'#8b5cf6', PLANNING:'#22c55e', COMPLETED:'#3b82f6', PAUSED:'#f59e0b', DROPPED:'#ef4444', REPEATING:'#a78bfa' };
    var PROFILE_STATUS_LABELS = { CURRENT:'Watching', PLANNING:'Planning', COMPLETED:'Completed', PAUSED:'Paused', DROPPED:'Dropped', REPEATING:'Repeating' };
    function profileListStatusOf(item) {
        // Prefer authoritative listData.status (AniList), then _listStatus/_listType, then state.listEntries by mediaId
        if (item && item.listData && item.listData.status) return String(item.listData.status).toUpperCase();
        if (item && item._listStatus) return String(item._listStatus).toUpperCase();
        if (item && item._listType) return String(item._listType).toUpperCase();
        if (item && item.mediaId && state.listEntries && state.listEntries[item.mediaId] && state.listEntries[item.mediaId].status) {
            return String(state.listEntries[item.mediaId].status).toUpperCase();
        }
        if (item && item._raw && item._raw.status) return String(item._raw.status).toUpperCase();
        if (item && item.status) return String(item.status).toUpperCase();
        return '';
    }
    function profileEmptyBuckets() {
        var by = {};
        PROFILE_STATUS.forEach(function (k) { by[k] = { titles: 0, episodes: 0, minutes: 0, scoreSum: 0, scored: 0 }; });
        return by;
    }
    // Counts per list status from the user's AniList collection (the same data the
    // Planning / Completed / ... sections on Home are built from, adult titles hidden
    // the same way), so the profile numbers always match those section headers.
    function profileComputeStats(lists) {
        var by = profileEmptyBuckets();
        var total = { titles: 0, episodes: 0, minutes: 0 };
        (lists || []).forEach(function (list) {
            if (!list || list.isCustomList || !list.status) return;
            var b = by[String(list.status).toUpperCase()];
            if (!b) return;
            (list.entries || []).forEach(function (en) {
                if (!en || !en.media || !en.media.id || isAdultMedia(en.media)) return;
                var prog = Number(en.progress) || 0;
                var dur = Number(en.media.duration) || 24;
                var score = normalizeScore(en.score);
                b.titles++; b.episodes += prog; b.minutes += prog * dur;
                if (score > 0) { b.scoreSum += score; b.scored++; }
                total.titles++; total.episodes += prog; total.minutes += prog * dur;
            });
        });
        return { byStatus: by, total: total };
    }
    function profileLibraryByStatus() {
        var map = {}; PROFILE_STATUS.forEach(function (k) { map[k] = 0; });
        if (state.profileStats) {
            PROFILE_STATUS.forEach(function (k) { map[k] = state.profileStats.byStatus[k].titles; });
            return map;
        }
        // fallback until the AniList collection has loaded: local library entries
        var libs = state.library || [];
        for (var i = 0; i < libs.length; i++) {
            var st = profileListStatusOf(libs[i]);
            if (map[st] != null) map[st]++;
        }
        return map;
    }
    function profileTotalTitles() {
        if (state.profileStats) return state.profileStats.total.titles;
        return (state.library || []).length;
    }
    function profileTimeWatched() {
        if (state.profileStats) {
            return { episodes: state.profileStats.total.episodes, minutes: state.profileStats.total.minutes };
        }
        var totalMin = 0, eps = 0;
        var libs = state.library || [];
        for (var i = 0; i < libs.length; i++) {
            var ld = libs[i].listData; if (!ld || typeof ld.progress !== 'number') continue;
            var prog = ld.progress; if (prog <= 0) continue;
            eps += prog;
            var dur = libs[i].episodeLength || (libs[i]._raw && libs[i]._raw.duration) || 24;
            totalMin += prog * dur;
        }
        return { episodes: eps, minutes: totalMin };
    }
    function profileRenderHeader() {
        var card = $('#profile-card'); if (!card) return;
        var libs = state.library || [];
        var titles = profileTotalTitles();
        var tw = profileTimeWatched();
        var hours = Math.floor(tw.minutes / 60), mins = Math.round(tw.minutes % 60);
        // name from first library entry with userPreferred title or fallback to Seanime
        var name = 'Seanime'; var avatar = '';
        for (var i = 0; i < libs.length; i++) {
            var raw = libs[i]._raw; if (!raw) continue;
            var u = (raw.user || raw.owner || raw.viewer || raw.creator);
            if (u && u.name) { name = u.name; avatar = (u.avatar && (u.avatar.large || u.avatar.medium)) || ''; break; }
        }
        // also try state.detail anime viewer
        if (name === 'Seanime' && state.listEntries) {
            // no viewer endpoint – keep server name
        }
        card.innerHTML = '';
        var wrap = document.createElement('div'); wrap.className = 'profile-card';
        var av = avatar ? document.createElement('img') : document.createElement('div');
        if (avatar) { av.src = avatar; av.alt = name; }
        else { av.style.width='96px'; av.style.height='96px'; av.style.borderRadius='50%'; av.style.background='#2a2a3a'; av.style.marginRight='20px'; av.style.display='flex'; av.style.alignItems='center'; av.style.justifyContent='center'; av.style.fontSize='36px'; av.style.fontWeight='700'; av.style.color='#a78bfa'; av.textContent = name.charAt(0).toUpperCase(); }
        if (!avatar) { /* div already styled */ } else { av.style.width='96px'; av.style.height='96px'; av.style.borderRadius='50%'; av.style.objectFit='cover'; av.style.marginRight='20px'; av.style.background='#1a1a28'; }
        // Tizen-safe: margin via style, not gap
        if (!av.style.marginRight) av.style.marginRight = '20px';
        var meta = document.createElement('div');
        meta.innerHTML = '<div style="font-size:28px;font-weight:700">' + escapeHtml(name) + '</div>' +
            '<div style="font-size:16px;color:#8888aa;margin-top:6px;">' + titles + ' titles · ' + tw.episodes + ' episodes · ' + hours + 'h ' + mins + 'm · ' + (connectionOnline ? 'Online' : 'Offline') + '</div>' +
            '<div style="font-size:13px;color:#6a6a82;margin-top:4px;">' + escapeHtml(CONFIG.serverUrl || '') + '</div>';
        wrap.appendChild(av); wrap.appendChild(meta); card.appendChild(wrap);
    }
    function profileRenderDistribution() {
        var host = $('#profile-bar'); if (!host) return;
        var byStatus = profileLibraryByStatus(); var total = 0;
        PROFILE_STATUS.forEach(function (k) { total += byStatus[k]; });
        host.innerHTML = ''; if (!total) return;
        var track = document.createElement('div'); track.className = 'profile-bar-track';
        PROFILE_STATUS.forEach(function (k) {
            var c = byStatus[k]; if (!c) return;
            var seg = document.createElement('div'); seg.className = 'profile-bar-seg';
            seg.style.width = ((c / total) * 100).toFixed(1) + '%';
            seg.style.background = PROFILE_STATUS_COLORS[k] || '#888';
            track.appendChild(seg);
        });
        var legend = document.createElement('div'); legend.className = 'profile-bar-legend';
        PROFILE_STATUS.forEach(function (k) {
            var c = byStatus[k]; if (!c) return;
            var sp = document.createElement('span');
            sp.innerHTML = '<span style="display:inline-block;width:10px;height:10px;border-radius:50%;background:' + (PROFILE_STATUS_COLORS[k] || '#888') + ';margin-right:6px;vertical-align:middle;"></span>' + PROFILE_STATUS_LABELS[k] + ' ' + c;
            legend.appendChild(sp);
        });
        host.appendChild(track); host.appendChild(legend);
    }
    function profileRenderActivity() {
        var host = $('#profile-activity'), section = $('#profile-activity-section');
        if (!host || !section) return;
        var libs = state.library || [];
        var sorted = libs.slice().sort(function (a, b) {
            var ta = (a.updatedAt != null ? a.updatedAt : (a._raw && a._raw.updatedAt != null ? a._raw.updatedAt : 0)) || 0;
            var tb = (b.updatedAt != null ? b.updatedAt : (b._raw && b._raw.updatedAt != null ? b._raw.updatedAt : 0)) || 0;
            if (tb !== ta) return tb - ta;
            return (b._order || 0) - (a._order || 0);
        }).slice(0, 8);
        host.innerHTML = ''; if (!sorted.length || !sorted[0].updatedAt && !sorted[0]._order) { section.style.display = 'none'; return; }
        section.style.display = '';
        sorted.forEach(function (item) {
            var row = document.createElement('div'); row.className = 'profile-activity-row'; row.tabIndex = 0;
            var thumb = document.createElement('img'); thumb.className = 'profile-activity-thumb';
            thumb.alt = item.title || ''; thumb.src = item.coverImage || item.posterLarge || '';
            var body = document.createElement('div');
            var ld = item.listData; var prog = ld && typeof ld.progress === 'number' ? ld.progress : 0;
            var total = item.episodes || '?';
            body.innerHTML = '<div class="profile-activity-title">' + escapeHtml(item.title || 'Unknown') + '</div>' +
                '<div class="profile-activity-meta">' + (ld ? escapeHtml(String(ld.status || '')) : '') + ' · Ep ' + prog + ' / ' + total + '</div>';
            row.appendChild(thumb); row.appendChild(body);
            row.addEventListener('click', function () { openAnimeDetail(item); });
            row.addEventListener('keydown', function (e) { if (e.keyCode === KEY_CODES.ENTER) { e.preventDefault(); openAnimeDetail(item); } });
            host.appendChild(row);
        });
    }
    function profileRenderCW() {} // removed per request
    function profileListStats() {
        if (state.profileStats) return state.profileStats.byStatus;
        // fallback until the AniList collection has loaded: local library entries
        var out = profileEmptyBuckets();
        var libs = state.library || [];
        for (var i = 0; i < libs.length; i++) {
            var st = profileListStatusOf(libs[i]);
            if (!out[st]) continue;
            out[st].titles++;
            var ld = libs[i].listData;
            if (ld && typeof ld.progress === 'number') { out[st].episodes += ld.progress; var dur = libs[i].episodeLength || 24; out[st].minutes += ld.progress * dur; }
            if (ld && typeof ld.score === 'number' && ld.score > 0) { out[st].scoreSum += normalizeScore(ld.score); out[st].scored++; }
        }
        return out;
    }
    function profileRenderListStats() {
        // one box per list (Watching, Planning, Completed, ...) with the number of shows in it
        var extra = document.getElementById('profile-liststats');
        if (!extra) {
            extra = document.createElement('div');
            extra.id = 'profile-liststats'; extra.className = 'profile-liststats';
            var statsHost = $('#profile-stats');
            if (statsHost && statsHost.parentNode) statsHost.parentNode.insertBefore(extra, statsHost.nextSibling);
            else return;
        }
        var stats = profileListStats();
        extra.innerHTML = '';
        PROFILE_STATUS.forEach(function (k) {
            var s = stats[k] || { titles: 0, episodes: 0, minutes: 0, scoreSum: 0, scored: 0 };
            var box = document.createElement('div');
            var avg = s.scored ? (s.scoreSum / s.scored).toFixed(1) : '\u2014';
            var hrs = Math.floor(s.minutes / 60);
            box.innerHTML = '<div class="profile-liststats-val">' + s.titles + '</div>' +
                '<div class="profile-liststats-label">' + PROFILE_STATUS_LABELS[k] + '</div>' +
                '<div class="profile-liststats-label" style="margin-top:6px;font-size:12px;">' + s.episodes + ' eps \u00B7 ' + hrs + 'h \u00B7 avg ' + avg + '</div>';
            extra.appendChild(box);
        });
    }
    function escapeHtml(s) { return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;'); }

    // Library: Recently Added (sorted by updatedAt desc, most recent first; falls back to reverse insertion)
    function renderLibraryToolbar() {} // no-op: filters removed per request
    function tsOf(x) {
        if (!x) return 0;
        var v = x.updatedAt;
        if (v == null && x._raw) v = x._raw.updatedAt != null ? x._raw.updatedAt : x._raw.updated_at;
        if (v == null && x._raw && x._raw.media) v = x._raw.media.updatedAt != null ? x._raw.media.updatedAt : x._raw.media.updated_at;
        if (v == null) return 0;
        if (typeof v === 'number') return v > 1e12 ? Math.floor(v / 1000) : v; // ms -> s
        if (typeof v === 'string') { var t = Date.parse(v); return t ? Math.floor(t / 1000) : 0; }
        return 0;
    }
    function libraryFilteredList() {
        var src = state.library || [];
        // tag insertion order once per render so fallback ordering is stable
        for (var oi = 0; oi < src.length; oi++) src[oi]._order = oi;
        var list = src.slice();
        var anyTs = false;
        for (var ii = 0; ii < list.length; ii++) if (tsOf(list[ii])) { anyTs = true; break; }
        if (!anyTs) { list.reverse(); return list; }
        list.sort(function (a, b) {
            var ta = tsOf(a), tb = tsOf(b);
            if (tb !== ta) return tb - ta;
            // second key: reverse insertion (newest push = last in source array)
            var oa = a._order != null ? a._order : 0, ob = b._order != null ? b._order : 0;
            if (ob !== oa) return ob - oa;
            return (a.title || '').localeCompare(b.title || '');
        });
        return list;
    }
    function renderLibraryFiltered() {
        var row = $('#library-row');
        if (!row) return;
        row.innerHTML = '';
        var list = libraryFilteredList();
        if (!list.length) {
            row.innerHTML = '<p class="empty-note">Your library is empty.</p>';
            return;
        }
        appendCardBatch(row, list, 0);
    }
    function renderCustomLists() {
        var host = $('#custom-lists');
        if (!host) return;
        host.innerHTML = '';
        (state.libCustom || []).forEach(function (list) {
            if (!list || !list.entries || !list.entries.length) return;
            var section = document.createElement('section');
            section.className = 'content-section';
            var title = document.createElement('h2');
            title.className = 'section-title';
            title.textContent = list.name || 'Custom';
            var cnt = document.createElement('span');
            cnt.className = 'section-count';
            cnt.textContent = String(list.entries.length);
            title.appendChild(cnt);
            var row = document.createElement('div');
            row.className = 'card-row';
            section.appendChild(title); section.appendChild(row);
            host.appendChild(section);
            var items = list.entries.map(function (entry) {
                return normalizeAnime({ media: entry.media, listData: { status: entry.status || list.status, progress: entry.progress || 0 } });
            }).filter(function (x) { return x && x.mediaId; });
            appendCardBatch(row, items, 0);
        });
    }
    function renderLibrary(list) {
        // backward compat: called with raw list from loader
        if (list) state.library = list;
        renderLibraryToolbar();
        renderLibraryFiltered();
        renderCustomLists();
    }

    // Large lists are rendered in batches (a "+N more" card loads the next batch)
    // so a few hundred posters do not choke the TV.
    var CARD_BATCH = 30;
    function appendCardBatch(row, items, start) {
        var end = Math.min(items.length, start + CARD_BATCH);
        var firstNew = null;
        var frag = document.createDocumentFragment();       // one insertion (one layout) per batch
        for (var i = start; i < end; i++) {
            var c = renderAnimeCard(items[i]);
            if (!firstNew) firstNew = c;
            frag.appendChild(c);
        }
        if (end < items.length) {
            var more = document.createElement('div');
            more.className = 'anime-card more-card';
            more.tabIndex = 0;
            more.textContent = '+' + (items.length - end) + ' more';
            var expand = function () {
                if (more.parentNode !== row) return;
                row.removeChild(more);
                var f = appendCardBatch(row, items, end);
                if (f) f.focus();
            };
            more.addEventListener('click', expand);
            more.addEventListener('focus', expand);          // reaching the end loads the next batch by itself
            more.addEventListener('keydown', function (e) {
                if (e.keyCode === KEY_CODES.ENTER) { e.preventDefault(); expand(); }
            });
            frag.appendChild(more);
        }
        row.appendChild(frag);
        return firstNew;
    }

    function renderSearchResults(list) {
        var row = $('#search-results-row');
        row.innerHTML = '';
        if (!list || list.length === 0) {
            row.innerHTML = '<p class="empty-note">No results</p>';
            return null;
        }
        return appendCardBatch(row, list, 0);
    }

    var searchSeq = 0;
    function clearSearchResults() {
        searchSeq++;
        state.searchResults = [];
        $('#search-results-row').innerHTML = '';
        $('#search-section').style.display = 'none';
    }
    function runSearch() {
        var q = ($('#search-input').value || '').trim();
        hideIME();
        if (!q) { clearSearchResults(); return; }
        setView('home');
        var seq = ++searchSeq;
        $('#search-section').style.display = 'block';
        $('#search-title').textContent = 'Results for \u201C' + q + '\u201D';
        $('#search-results-row').innerHTML = '<p class="empty-note">Searching\u2026</p>';
        $('#content-area').scrollTop = 0;
        api.search(q).then(function (results) {
            if (seq !== searchSeq) return;
            state.searchResults = results.map(normalizeAnime).filter(function (x) { return x && x.mediaId; });
            var first = renderSearchResults(state.searchResults);
            if (first) first.focus();
        }).catch(function (e) {
            if (seq !== searchSeq) return;
            console.error('[Search] failed:', e);
            $('#search-results-row').innerHTML = '<p class="empty-note">Search failed: ' +
                String((e && e.message) || e).replace(/</g, '&lt;') + '</p>';
        });
    }

    // ===== Status sections (AniList list statuses) =====
    var STATUS_SECTIONS = [
        { key: 'PLANNING',  title: 'Planning' },
        { key: 'COMPLETED', title: 'Completed' },
        { key: 'REPEATING', title: 'Repeating' },
        { key: 'PAUSED',    title: 'Paused' },
        { key: 'DROPPED',   title: 'Dropped' }
    ];

    function renderStatusSections(lists) {
        var host = $('#status-sections');
        if (!host) return;
        host.innerHTML = '';
        var byStatus = {};
        (lists || []).forEach(function (list) {
            if (!list || list.isCustomList || !list.status) return;
            var items = (list.entries || []).map(function (entry) {
                if (!entry || !entry.media) return null;
                return normalizeAnime({
                    media: entry.media,
                    listData: { status: entry.status || list.status, progress: entry.progress || 0 }
                });
            }).filter(function (x) { return x && x.mediaId; });
            byStatus[list.status] = (byStatus[list.status] || []).concat(items);
        });
        STATUS_SECTIONS.forEach(function (def) {
            var items = byStatus[def.key];
            if (!items || items.length === 0) return;
            var section = document.createElement('section');
            section.className = 'content-section';
            var title = document.createElement('h2');
            title.className = 'section-title';
            title.textContent = def.title;
            var count = document.createElement('span');
            count.className = 'section-count';
            count.textContent = String(items.length);
            title.appendChild(count);
            var row = document.createElement('div');
            row.className = 'card-row';
            section.appendChild(title);
            section.appendChild(row);
            host.appendChild(section);
            appendCardBatch(row, items, 0);
        });
    }

    function loadStatusSections() {
        return api.getAnimeCollection().then(function (lists) {
            DEBUG && console.log('[API] AniList collection lists:', lists.length);
            var map = {}, entries = {}, blocked = {};
            var customs = [];
            lists.forEach(function (list) {
                if (list.isCustomList) {
                    if (list.entries && list.entries.length) customs.push(list);
                    return;
                }
                if (!list.status) return;
                (list.entries || []).forEach(function (en) {
                    if (en && en.media && en.media.id) {
                        if (isAdultMedia(en.media)) blocked[en.media.id] = true;
                        map[en.media.id] = en.progress || 0;
                        entries[en.media.id] = { status: en.status || list.status, progress: en.progress || 0, score: normalizeScore(en.score) };
                    }
                });
            });
            state.libCustom = customs;
            state.listProgress = map;
            state.listEntries = entries;
            state.blockedIds = blocked;
            state.listProgressLoaded = true;
            state.profileStats = profileComputeStats(lists);
            renderStatusSections(lists);
            renderCustomLists();
            renderLibraryToolbar();
            if (state.view === 'profile') profileRenderSummary();   // counts arrived while the profile is open
        }).catch(function (e) {
            console.warn('[API] AniList collection failed:', e);
        });
    }

    // ===== Detail Screen =====
    var LIST_STATUSES = [
        { v: 'CURRENT', l: 'Watching' }, { v: 'PLANNING', l: 'Planning' }, { v: 'COMPLETED', l: 'Completed' },
        { v: 'PAUSED', l: 'On hold' }, { v: 'DROPPED', l: 'Dropped' }, { v: 'REPEATING', l: 'Rewatching' }
    ];
    var MEDIA_STATUS = { FINISHED: 'Finished', RELEASING: 'Airing', NOT_YET_RELEASED: 'Upcoming', CANCELLED: 'Cancelled', HIATUS: 'On hiatus' };
    var MONTHS = ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec'];
    var STAR_SVG = '<svg viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><path d="M12 2.5l2.9 6.1 6.6.8-4.9 4.6 1.3 6.6L12 17.3l-5.9 3.3 1.3-6.6L2.5 9.4l6.6-.8z"/></svg>';

    function listStatusLabel(v) {
        for (var i = 0; i < LIST_STATUSES.length; i++) if (LIST_STATUSES[i].v === v) return LIST_STATUSES[i].l;
        return v || '';
    }
    // AniList scores come back in the user's score format; this app shows 0-10.
    function normalizeScore(v) {
        var n = Number(v) || 0;
        return n > 10 ? Math.round(n) / 10 : n;
    }
    function formatAirDate(str) {
        var m = String(str || '').match(/^(\d{4})-(\d{2})-(\d{2})/);
        return m ? MONTHS[parseInt(m[2], 10) - 1] + ' ' + parseInt(m[3], 10) + ', ' + m[1] : '';
    }
    function cleanDescription(html) {
        return String(html || '')
            .replace(/<br\s*\/?>/gi, '\n').replace(/<[^>]*>/g, '')
            .replace(/&amp;/g, '&').replace(/&quot;/g, '"').replace(/&#0?39;/g, "'")
            .replace(/&lt;/g, '<').replace(/&gt;/g, '>')
            .replace(/\n{3,}/g, '\n\n').replace(/^\s+|\s+$/g, '');
    }
    function formatCountdown(sec) {
        var d = Math.floor(sec / 86400), h = Math.floor((sec % 86400) / 3600), m = Math.floor((sec % 3600) / 60);
        if (d > 0) return d + (d === 1 ? ' day' : ' days') + (h ? ' ' + h + ' h' : '');
        if (h > 0) return h + ' h ' + m + ' min';
        return Math.max(m, 1) + ' min';
    }

    // The user's list data for the anime shown on the detail screen (null = not on a list).
    function currentListData(anime) {
        var d = state.detail;
        var src = (d && d.entryLoaded) ? d.entryListData : (state.listEntries[anime.mediaId] || null);
        if (!src || !src.status) return null;
        return { status: src.status, progress: src.progress || 0, score: normalizeScore(src.score) };
    }

    function detailEpisodes() {
        var d = state.detail;
        return (d && state.bundle && state.bundle.mediaId === d.mediaId) ? state.bundle.episodes : [];
    }
    function detailTotalEpisodes() {
        var d = state.detail;
        if (!d) return 0;
        var max = 0;
        detailEpisodes().forEach(function (ep, i) {
            var n = ep.episodeNumber || ep.number || (i + 1);
            if (n > max) max = n;
        });
        return max || d.anime.episodes || 0;
    }

    function addChip(container, text, cls, html) {
        var chip = document.createElement('span');
        chip.className = 'chip' + (cls ? ' ' + cls : '');
        if (html) chip.innerHTML = html + '<span></span>';
        var target = html ? chip.lastChild : chip;
        target.textContent = text;
        container.appendChild(chip);
    }

    function renderDetailChips(anime) {
        var chips = $('#detail-chips'), genres = $('#detail-genres');
        chips.innerHTML = '';
        genres.innerHTML = '';
        if (anime.meanScore) addChip(chips, (anime.meanScore / 10).toFixed(1), 'score', STAR_SVG);
        if (anime.format) addChip(chips, String(anime.format).replace(/_/g, ' '));
        if (anime.year) addChip(chips, String(anime.year));
        if (anime.episodes) addChip(chips, anime.episodes + (anime.episodes === 1 ? ' episode' : ' episodes'));
        if (anime.episodeLength) addChip(chips, anime.episodeLength + ' min');
        if (anime.status) addChip(chips, MEDIA_STATUS[anime.status] || anime.status);
        (anime.genres || []).forEach(function (g) { addChip(genres, g, 'genre'); });
    }

    function renderDetailMeta() {
        var d = state.detail;
        if (!d) return;
        var parts = [];
        if (d.studios) parts.push(d.studios);
        var na = d.anime.nextAiring;
        if (na && na.episode && na.timeUntilAiring > 0) parts.push('Episode ' + na.episode + ' airs in ' + formatCountdown(na.timeUntilAiring));
        $('#detail-meta').textContent = parts.join('   \u00B7   ');
    }

    // Play button ("Continue \u00B7 Episode N") and list button ("Watching \u00B7 3/12")
    function updateDetailActions() {
        var d = state.detail;
        if (!d) return;
        var ld = currentListData(d.anime);
        var progress = ld ? ld.progress : 0;
        var total = detailTotalEpisodes();
        var target = progress + 1, label;
        if (total && progress >= total) { target = 1; label = 'Rewatch from episode 1'; }
        else if (progress > 0) label = 'Continue \u00B7 Episode ' + target;
        else { target = 1; label = 'Play \u00B7 Episode 1'; }
        d.playTarget = target;
        $('#detail-play').textContent = label;
        $('#detail-list').textContent = ld
            ? listStatusLabel(ld.status) + '   \u00B7   ' + progress + (total ? '/' + total : '')
            : '+ Add to list';
    }

    // Fills gaps in a sparse anime object (opened from the schedule or a recommendation).
    function enrichAnimeFromDetails(anime, det) {
        var changed = false;
        if (!anime.description && det.description) { anime.description = det.description; changed = true; }
        if ((!anime.genres || !anime.genres.length) && det.genres && det.genres.length) { anime.genres = det.genres; changed = true; }
        if (!anime.meanScore && det.meanScore) { anime.meanScore = det.meanScore; changed = true; }
        if (!anime.year && det.startDate && det.startDate.year) { anime.year = det.startDate.year; changed = true; }
        if (!anime.episodeLength && det.duration) { anime.episodeLength = det.duration; changed = true; }
        return changed;
    }

    function mapLimit(items, limit, fn) {
        return new Promise(function (resolve) {
            var results = new Array(items.length), next = 0, running = 0, finished = 0;
            if (!items.length) { resolve([]); return; }
            function launch() {
                while (running < limit && next < items.length) {
                    (function (i) {
                        running++;
                        fn(items[i]).then(function (v) { results[i] = v; }, function () { results[i] = null; }).then(function () {
                            running--; finished++;
                            if (finished === items.length) resolve(results); else launch();
                        });
                    })(next++);
                }
            }
            launch();
        });
    }

    // "More like this": AniList recommendations. Their data has no genres, so every
    // candidate is looked up once to apply the same adult/ecchi filter as everywhere else
    // (a title that cannot be checked is not shown).
    function loadRecommendations(mediaId, details) {
        var edges = (details && details.recommendations && details.recommendations.edges) || [];
        var nodes = [];
        edges.forEach(function (e) {
            var n = e && e.node && e.node.mediaRecommendation;
            if (n && n.id && n.id !== mediaId && !n.isAdult && (!n.type || n.type === 'ANIME')) nodes.push(n);
        });
        nodes = nodes.slice(0, 12);
        if (!nodes.length) return;
        mapLimit(nodes, 4, function (n) {
            return api.getMediaDetails(n.id).then(function (det) {
                if (!det || isAdultMedia({ isAdult: n.isAdult, genres: det.genres })) return null;
                var a = normalizeAnime(n);
                a.genres = det.genres || [];
                return a;
            });
        }).then(function (list) {
            if (!state.detail || state.detail.mediaId !== mediaId) return;
            var items = list.filter(function (x) { return x && x.mediaId; });
            var row = $('#detail-recs');
            row.innerHTML = '';
            $('#recs-title').style.display = items.length ? '' : 'none';
            if (items.length) appendCardBatch(row, items, 0);
        });
    }

    // P0.3 - Detail helpers: cast/staff/relations/characters
    function renderCastRow(containerId, titleId, items, kind) {
        var row = $('#' + containerId), ttl = $('#' + titleId);
        if (!row || !ttl) return;
        row.innerHTML = '';
        if (!items || !items.length) { ttl.style.display = 'none'; return; }
        ttl.style.display = '';
        items.slice(0, 16).forEach(function (it) {
            var card = document.createElement('div');
            card.className = 'cast-card'; card.tabIndex = 0;
            var img = document.createElement('img');
            img.alt = it.name || '';
            lazyImage(img, it.image || '');
            var info = document.createElement('div');
            info.className = 'cast-info';
            var name = document.createElement('div'); name.className = 'cast-name'; name.textContent = it.name || 'Unknown';
            var role = document.createElement('div'); role.className = 'cast-role'; role.textContent = it.role || it.character || '';
            info.appendChild(name); if (role.textContent) info.appendChild(role);
            card.appendChild(img); card.appendChild(info);
            row.appendChild(card);
        });
    }
    function loadDetailMeta(mediaId) {
        return api.getMediaDetails(mediaId).then(function (details) {
            if (!state.detail || state.detail.mediaId !== mediaId || !details) return null;
            return details;
        });
    }
    function renderRelations(mediaId, details) {
        var edges = (details && details.relations && details.relations.edges) || [];
        var nodes = [];
        edges.forEach(function (e) {
            var m = e && e.node;
            if (!m || !m.id || m.id === mediaId) return;
            if (m.isAdult) return;
            var a = normalizeAnime(m);
            if (a) { a.relationType = e.relationType || ''; nodes.push(a); }
        });
        var row = $('#detail-relations'), ttl = $('#relations-title');
        if (!row || !ttl) return;
        row.innerHTML = '';
        if (!nodes.length) { ttl.style.display = 'none'; return; }
        ttl.style.display = '';
        appendCardBatch(row, nodes.slice(0, 20), 0);
    }

    function openAnimeDetail(anime, isBack) {
        var mediaId = anime.mediaId;
        if (!isBack) {
            if (state.currentScreen === 'detail' && state.detail) state.detailStack.push(state.detail.anime);
            else state.detailStack = [];
        }
        $('#recs-title').style.display = 'none';
        $('#detail-recs').innerHTML = '';
        $('#cast-title').style.display = 'none'; $('#detail-cast').innerHTML = '';
        $('#staff-title').style.display = 'none'; $('#detail-staff').innerHTML = '';
        $('#relations-title').style.display = 'none'; $('#detail-relations').innerHTML = '';
        state.currentAnime = anime;
        state.detail = { mediaId: mediaId, anime: anime, entryListData: null, entryLoaded: false, studios: '', playTarget: 1 };
        closeListPanel(true);

        var posterImg = $('#detail-poster-img');
        posterImg.onerror = null;
        lazyImage(posterImg, [anime.posterLarge, anime.coverImage]);
        var detailBg = $('#detail-backdrop');
        detailBg.style.backgroundImage = 'none';             // do not show the previous title's backdrop
        setBackdrop(detailBg, [anime.bannerImage, anime.coverImage]);
        $('#detail-title').textContent = anime.title;
        renderDetailChips(anime);
        renderDetailMeta();
        $('#detail-synopsis').textContent = anime.description ? cleanDescription(anime.description) : 'No synopsis available.';
        $('#episode-list').innerHTML = '<p class="empty-note">Loading episodes\u2026</p>';
        updateDetailActions();
        showScreen('detail');
        $('#detail-content').scrollTop = 0;
        try { $('#detail-play').focus(); } catch (e) {}

        // episodes + files on disk + the user's list data
        loadEpisodeBundle(anime, true).then(function (bundle) {
            if (!state.detail || state.detail.mediaId !== mediaId) return;
            if (bundle.entry) {
                var ld = bundle.entry.listData;
                state.detail.entryLoaded = true;
                state.detail.entryListData = (ld && ld.status)
                    ? { status: ld.status, progress: ld.progress || 0, score: normalizeScore(ld.score) } : null;
            }
            renderEpisodeList(bundle.episodes);
            updateDetailActions();
        });

        api.getMediaDetails(mediaId).then(function (details) {
            if (!state.detail || state.detail.mediaId !== mediaId || !details) return;
            var nodes = (details.studios && details.studios.nodes) || [];
            state.detail.studios = nodes.slice(0, 2).map(function (n) { return n.name; }).join(', ');
            if (enrichAnimeFromDetails(anime, details)) {
                if (isAdultMedia({ genres: anime.genres })) {
                    showAppToast('This title is hidden');
                    state.detailStack = [];
                    showScreen('home');
                    return;
                }
                renderDetailChips(anime);
                $('#detail-synopsis').textContent = anime.description ? cleanDescription(anime.description) : 'No synopsis available.';
            }
            renderDetailMeta();
            loadRecommendations(mediaId, details);
            renderRelations(mediaId, details);
            // characters
            var chars = (details.characters && details.characters.edges) || [];
            var cast = [];
            chars.slice(0, 16).forEach(function (e) {
                var ch = e && e.node, va = e && e.voiceActors && e.voiceActors[0];
                if (!ch) return;
                cast.push({ name: ch.name && (ch.name.full || ch.name.userPreferred) || 'Unknown', role: ch.role || e.role || '', image: ch.image && (ch.image.large || ch.image.medium) || (va && va.image && va.image.large) || '' });
            });
            renderCastRow('detail-cast', 'cast-title', cast);
            // staff
            var staffEdges = (details.staff && details.staff.edges) || [];
            var staff = [];
            staffEdges.slice(0, 12).forEach(function (e) {
                var s = e && e.node;
                if (!s) return;
                staff.push({ name: s.name && (s.name.full || s.name.userPreferred) || 'Unknown', role: e.role || '', image: s.image && (s.image.large || s.image.medium) || '' });
            });
            renderCastRow('detail-staff', 'staff-title', staff);
        }).catch(function () {});
    }

    // Long series (hundreds of episodes, each with a thumbnail and a summary) used to be built
    // in one go: thousands of DOM nodes and image objects on a TV. Now EP_BATCH at a time;
    // moving DOWN past the last row (handleDetailKeys) appends the next batch.
    var EP_BATCH = 40;
    function renderEpisodeList(episodes) {
        var list = $('#episode-list');
        list.innerHTML = '';
        list._eps = null;
        if (!episodes || episodes.length === 0) {
            list.innerHTML = '<p class="empty-note">No episodes found</p>';
            return;
        }
        var ld = state.detail ? currentListData(state.detail.anime) : null;
        var progress = ld ? ld.progress : 0;
        var total = detailTotalEpisodes();
        var completed = total && progress >= total;
        list._eps = { eps: episodes, next: 0, progress: progress, completed: completed };
        appendEpisodeBatch();
    }

    function appendEpisodeBatch() {
        var list = $('#episode-list'), ctx = list && list._eps;
        if (!ctx || ctx.next >= ctx.eps.length) return false;
        var end = Math.min(ctx.eps.length, ctx.next + EP_BATCH);
        var frag = document.createDocumentFragment();
        for (var i = ctx.next; i < end; i++) frag.appendChild(buildEpisodeItem(ctx.eps[i], i, ctx));
        ctx.next = end;
        list.appendChild(frag);
        return true;
    }

    function buildEpisodeItem(ep, index, ctx) {
            var progress = ctx.progress, completed = ctx.completed;
            var number = ep.episodeNumber || ep.number || (index + 1);
            var meta = ep.episodeMetadata || {};
            var item = document.createElement('div');
            item.className = 'episode-item' + (number <= progress ? ' watched' : (!completed && number === progress + 1 ? ' next-up' : ''));
            item.tabIndex = 0;

            var thumb = document.createElement('div');
            thumb.className = 'ep-thumb';
            if (meta.image) {
                var img = document.createElement('img');
                img.alt = '';
                lazyImage(img, meta.image);
                thumb.appendChild(img);
            }
            if (number <= progress) {
                var seen = document.createElement('span');
                seen.className = 'ep-watched';
                seen.innerHTML = CHECK_SVG;
                thumb.appendChild(seen);
            }

            var body = document.createElement('div');
            body.className = 'ep-body';
            var head = document.createElement('div');
            head.className = 'ep-head';
            var num = document.createElement('span');
            num.className = 'ep-number';
            num.textContent = 'EP ' + number;
            var title = document.createElement('span');
            title.className = 'ep-title';
            title.textContent = ep.episodeTitle || ep.title || ep.displayTitle || ('Episode ' + number);
            head.appendChild(num); head.appendChild(title);

            var sub = document.createElement('div');
            sub.className = 'ep-sub';
            var mins = ep.duration || meta.length || 0;
            var bits = [];
            if (mins) bits.push(Math.floor(mins) + ' min');
            var aired = formatAirDate(meta.airDate);
            if (aired) bits.push(aired);
            sub.textContent = bits.join('  \u00B7  ');
            if (ep.localFile) {
                var badge = document.createElement('span');
                badge.className = 'ep-badge';
                badge.textContent = 'On disk';
                sub.appendChild(badge);
            }
            body.appendChild(head);
            if (bits.length || ep.localFile) body.appendChild(sub);
            var summary = meta.summary || meta.overview;
            if (summary) {
                var sum = document.createElement('div');
                sum.className = 'ep-summary';
                sum.textContent = summary;
                body.appendChild(sum);
            }

            item.appendChild(thumb);
            item.appendChild(body);
            item.addEventListener('click', function () { playEpisode(ep, index); });
            item._epIndex = index;
            return item;
    }

    function playEpisode(episode, index) {
        var anime = state.currentAnime;
        if (!anime) return;
        state.playbackOrigin = 'detail';
        state.currentEpisodeIndex = index;
        playEpisodeAuto(anime, episode.episodeNumber || episode.number || (index + 1), episode);
    }

    function playDetailTarget() {
        var d = state.detail;
        if (!d) return;
        ensureEpisodes(d.anime).then(function () {
            var episodes = detailEpisodes();
            var info = null;
            episodes.forEach(function (ep, i) {
                if ((ep.episodeNumber || ep.number || (i + 1)) === d.playTarget) info = ep;
            });
            if (!info && episodes.length) {
                // fallback: first episode if playTarget not found (metadata still loading)
                info = episodes[d.playTarget - 1] || episodes[0];
            }
            state.playbackOrigin = 'detail';
            state.currentAnime = d.anime;
            playEpisodeAuto(d.anime, (info && (info.episodeNumber || info.number)) || d.playTarget, info || { aniDBEpisode: null });
        }).catch(function () {
            // episodes failed to load but still try torrent search with playTarget number
            state.playbackOrigin = 'detail';
            state.currentAnime = d.anime;
            playEpisodeAuto(d.anime, d.playTarget, { aniDBEpisode: null });
        });
    }

    // ----- My list editor -----
    function openListPanel() {
        var d = state.detail;
        if (!d) return;
        var ld = currentListData(d.anime);
        state.listEdit = {
            inList: !!ld,
            total: detailTotalEpisodes(),
            draft: ld ? { status: ld.status, progress: ld.progress, score: Math.round(ld.score) }
                      : { status: 'PLANNING', progress: 0, score: 0 },
            removeArmedUntil: 0,
            saving: false
        };
        $('#list-panel-title').textContent = ld ? 'My list' : 'Add to my list';
        renderListPanel(0);
        $('#list-panel').classList.remove('hidden');
    }

    function closeListPanel(silent) {
        state.listEdit = null;
        var panel = $('#list-panel');
        if (panel) panel.classList.add('hidden');
        if (!silent) { try { $('#detail-list').focus(); } catch (e) {} }
    }

    function listFieldLabel(le, field) {
        var d = le.draft;
        if (field === 'status') return listStatusLabel(d.status);
        if (field === 'score') return d.score > 0 ? d.score + ' / 10' : 'Not scored';
        return d.progress + (le.total ? ' / ' + le.total : '');
    }

    function renderListPanel(focusIndex) {
        var le = state.listEdit;
        if (!le) return;
        var box = $('#list-panel-rows');
        box.innerHTML = '';
        function field(key, label) {
            var row = document.createElement('div');
            row.className = 'setting-row setting-focusable';
            row.tabIndex = 0;
            row._field = key;
            row.innerHTML = '<span class="setting-label"></span><span class="setting-value">' +
                '<span class="set-arrow">' + CHEV_L + '</span><span class="set-val"></span><span class="set-arrow">' + CHEV_R + '</span></span>';
            row.querySelector('.setting-label').textContent = label;
            row.querySelector('.set-val').textContent = listFieldLabel(le, key);
            row.addEventListener('click', function () { activateListRow(row); });
            box.appendChild(row);
        }
        function action(key, label, cls) {
            var row = document.createElement('div');
            row.className = 'setting-row setting-focusable setting-action' + (cls ? ' ' + cls : '');
            row.tabIndex = 0;
            row._action = key;
            row.innerHTML = '<span class="setting-label"></span><span class="setting-value"></span>';
            row.querySelector('.setting-label').textContent = label;
            row.addEventListener('click', function () { activateListRow(row); });
            box.appendChild(row);
        }
        field('status', 'Status');
        field('score', 'Score');
        field('progress', 'Episodes watched');
        action('save', le.saving ? 'Saving\u2026' : 'Save');
        if (le.inList) action('remove', 'Remove from my list', 'danger');
        var rows = box.querySelectorAll('.setting-focusable');
        var f = rows[Math.min(focusIndex || 0, rows.length - 1)];
        if (f) { try { f.focus(); } catch (e) {} }
    }

    function changeListField(row, delta) {
        var le = state.listEdit, d = le.draft, field = row._field;
        if (!le || !field) return;
        if (field === 'status') {
            var idx = 0;
            for (var i = 0; i < LIST_STATUSES.length; i++) if (LIST_STATUSES[i].v === d.status) idx = i;
            d.status = LIST_STATUSES[(idx + delta + LIST_STATUSES.length) % LIST_STATUSES.length].v;
            if (d.status === 'COMPLETED' && le.total) d.progress = le.total;
        } else if (field === 'score') {
            d.score = Math.max(0, Math.min(10, d.score + delta));
        } else {
            d.progress = Math.max(0, Math.min(le.total || 9999, d.progress + delta));
        }
        var rows = $('#list-panel-rows').querySelectorAll('.setting-focusable');
        var at = 0;
        for (var r = 0; r < rows.length; r++) if (rows[r] === row) at = r;
        renderListPanel(at);
    }

    function activateListRow(row) {
        var le = state.listEdit;
        if (!le) return;
        if (row._field) { changeListField(row, 1); return; }
        if (row._action === 'save') { saveListEdit(); return; }
        if (row._action === 'remove') {
            if (Date.now() < le.removeArmedUntil) { removeFromList(); return; }
            le.removeArmedUntil = Date.now() + 4000;
            var v = row.querySelector('.setting-value');
            v.innerHTML = '<span class="set-val"></span>';
            v.firstChild.textContent = 'Press OK again to remove';
        }
    }

    function afterListChange(data) {
        var d = state.detail;
        var id = d.mediaId;
        if (data) {
            state.listEntries[id] = data;
            state.listProgress[id] = data.progress;
            d.entryListData = data;
        } else {
            delete state.listEntries[id];
            delete state.listProgress[id];
            d.entryListData = null;
        }
        d.entryLoaded = true;
        state.needsRefresh = true;       // home rows reload when you go back
        closeListPanel();
        updateDetailActions();
        renderEpisodeList(detailEpisodes());
    }

    function saveListEdit() {
        var le = state.listEdit, d = state.detail;
        if (!le || !d || le.saving) return;
        le.saving = true;
        renderListPanel(3);
        var draft = le.draft;
        api.editListEntry({
            mediaId: d.mediaId, status: draft.status, score: Math.round(draft.score * 10),
            progress: draft.progress, type: 'anime'
        }).then(function () {
            afterListChange({ status: draft.status, progress: draft.progress, score: draft.score });
            showAppToast('Saved to your list');
        }).catch(function (e) {
            console.error('[List] save failed:', e);
            if (state.listEdit) { state.listEdit.saving = false; renderListPanel(3); }
            showAppToast('Could not save: ' + ((e && e.message) || e), 5000);
        });
    }

    function removeFromList() {
        var d = state.detail;
        if (!d) return;
        api.deleteListEntry(d.mediaId).then(function () {
            afterListChange(null);
            showAppToast('Removed from your list');
        }).catch(function (e) {
            console.error('[List] remove failed:', e);
            showAppToast('Could not remove: ' + ((e && e.message) || e), 5000);
        });
    }

    // Detail screen navigation: [Play] [My list] on top, then one row per episode.
    function handleDetailKeys(keyCode, e) {
        var K = KEY_CODES;
        if (state.listEdit) {
            var rows = $('#list-panel-rows').querySelectorAll('.setting-focusable');
            var cur = document.activeElement, at = -1;
            for (var i = 0; i < rows.length; i++) if (rows[i] === cur) at = i;
            if (keyCode === K.UP || keyCode === K.DOWN) {
                e.preventDefault();
                var next = Math.max(0, Math.min(rows.length - 1, (at < 0 ? 0 : at + (keyCode === K.DOWN ? 1 : -1))));
                if (rows[next]) rows[next].focus();
            } else if ((keyCode === K.LEFT || keyCode === K.RIGHT) && at >= 0 && rows[at]._field) {
                e.preventDefault();
                changeListField(rows[at], keyCode === K.RIGHT ? 1 : -1);
            } else if (keyCode === K.ENTER && at >= 0) {
                e.preventDefault();
                activateListRow(rows[at]);
            } else if (keyCode === K.RETURN) {
                closeListPanel();
            } else {
                e.preventDefault();
            }
            return true;
        }

        // Cast / Staff quick LEFT/RIGHT inside their row (cast-card)
        var actCast = document.activeElement;
        if (actCast && actCast.classList && actCast.classList.contains('cast-card')) {
            if (keyCode === K.LEFT || keyCode === K.RIGHT) {
                e.preventDefault();
                var st = keyCode === K.RIGHT ? 'nextElementSibling' : 'previousElementSibling';
                var sibC = actCast[st];
                while (sibC && !sibC.classList.contains('cast-card')) sibC = sibC[st];
                if (sibC) sibC.focus();
                return true;
            }
            if (keyCode === K.UP || keyCode === K.DOWN) {
                // fall through to grid navigation below
            } else {
                e.preventDefault();
                return true;
            }
        }

        // Episode rows: move between neighbours instead of rebuilding a grid of every episode
        // on each key press (a long series has hundreds).
        var act = document.activeElement;
        if (act && act.classList && act.classList.contains('episode-item')) {
            if (keyCode === K.UP || keyCode === K.DOWN) {
                e.preventDefault();
                var nb = keyCode === K.DOWN ? act.nextElementSibling : act.previousElementSibling;
                if (!nb && keyCode === K.DOWN && appendEpisodeBatch()) nb = act.nextElementSibling;
                if (nb) nb.focus();
                else if (keyCode === K.DOWN) {
                    var nextCast = document.querySelector('#detail-cast .cast-card');
                    var nextRel = document.querySelector('#detail-relations .anime-card');
                    var nextRec = document.querySelector('#detail-recs .anime-card');
                    var nxt = nextCast || nextRel || nextRec;
                    if (nxt) nxt.focus();
                }
                else { $('#detail-play').focus(); $('#detail-content').scrollTop = 0; }
                return true;
            }
            if (keyCode === K.LEFT) { e.preventDefault(); return true; }
            if (keyCode === K.RIGHT) {
                e.preventDefault();
                if (act._epIndex != null) openPickerForEpisode(act._epIndex);   // manual torrent choice
                return true;
            }
            if (keyCode === K.ENTER) {
                e.preventDefault();
                if (!e.target || e.target === act) act.click();
                return true;
            }
        }

        var grid = [[$('#detail-play'), $('#detail-list')]];
        var items = document.querySelectorAll('#episode-list .episode-item');
        for (var n = 0; n < items.length; n++) grid.push([items[n]]);
        var epRows = items.length;
        // Bug 4: include cast/staff (cast-row) and relations/recs (card-row) so D-pad UP/DOWN traverses them
        var castCards = document.querySelectorAll('#detail-cast .cast-card');
        if (castCards.length) {
            var cr = []; for (var qc = 0; qc < castCards.length; qc++) cr.push(castCards[qc]);
            grid.push(cr);
        }
        var staffCards = document.querySelectorAll('#detail-staff .cast-card');
        if (staffCards.length) {
            var sr = []; for (var qs = 0; qs < staffCards.length; qs++) sr.push(staffCards[qs]);
            grid.push(sr);
        }
        var relCards = document.querySelectorAll('#detail-relations .anime-card');
        if (relCards.length) {
            var relRow = []; for (var qr = 0; qr < relCards.length; qr++) relRow.push(relCards[qr]);
            grid.push(relRow);
        }
        var recs = document.querySelectorAll('#detail-recs .anime-card');
        if (recs.length) {
            var recRow = [];
            for (var q = 0; q < recs.length; q++) recRow.push(recs[q]);
            grid.push(recRow);
        }
        var active = document.activeElement, r = -1, c = 0;
        grid.forEach(function (row, ri) { row.forEach(function (el, ci) { if (el === active) { r = ri; c = ci; } }); });

        if (keyCode === K.UP || keyCode === K.DOWN) {
            e.preventDefault();
            var nr = r < 0 ? 0 : Math.max(0, Math.min(grid.length - 1, r + (keyCode === K.DOWN ? 1 : -1)));
            var target = grid[nr][Math.min(c, grid[nr].length - 1)];
            if (target) target.focus();
            if (nr === 0) $('#detail-content').scrollTop = 0;
            return true;
        }
        if (keyCode === K.LEFT || keyCode === K.RIGHT) {
            e.preventDefault();
            if (r >= 0 && grid[r].length > 1) {
                var nc = Math.max(0, Math.min(grid[r].length - 1, c + (keyCode === K.RIGHT ? 1 : -1)));
                grid[r][nc].focus();
            } else if (keyCode === K.RIGHT && r >= 1 && r <= epRows) {
                openPickerForEpisode(r - 1);          // manual torrent choice for this episode
            }
            return true;
        }
        if (keyCode === K.ENTER && active && active.click) {
            e.preventDefault();
            // a card with its own Enter handler (recommendations) has already acted and moved the focus
            if (!e.target || e.target === active) active.click();
            return true;
        }
        return false;
    }

    // ===== Torrent Loading Overlay =====
    var SLOW_START_SECONDS = 20;     // without any download speed for this long, suggest another torrent

    // While a stream starts, Seanime pushes {type:"torrentstream-state", payload:{state, data}}:
    //   state "loading" -> data names the stage (SEARCHING_TORRENTS, ADDING_TORRENT, ...)
    //   state "status"  -> data holds {downloadSpeed:"1.2 MB/s", progressPercentage, seeders, size, ...}
    // Those names come from Seanime's torrentstream package. They are looked up by name anywhere in
    // the payload, so a small difference between server versions only costs a field, not the feature
    // (switch DEBUG on to see the raw events in the console).
    var TORRENT_STAGES = {
        SEARCHING_TORRENTS:             { text: 'Searching for torrents\u2026',   floor: 6 },
        CHECKING_TORRENT_STATUS:        { text: 'Checking the torrent\u2026',     floor: 18 },
        ADDING_TORRENT:                 { text: 'Adding the torrent\u2026',       floor: 30 },
        SELECTING_FILE:                 { text: 'Selecting the video file\u2026', floor: 45 },
        STARTING_SERVER:                { text: 'Starting the stream\u2026',      floor: 60 },
        SENDING_STREAM_TO_MEDIA_PLAYER: { text: 'Stream ready, opening\u2026',    floor: 75 }
    };
    var TORRENT_STAGE_RE = /SEARCHING_TORRENTS|CHECKING_TORRENT_STATUS|ADDING_TORRENT|SELECTING_FILE|STARTING_SERVER|SENDING_STREAM_TO_MEDIA_PLAYER/;

    function setText(el, text) {
        if (el && el.textContent !== text) el.textContent = text;
    }

    // First value stored under any of `names`, looking up to 3 levels into the payload.
    function pickField(obj, names, depth) {
        if (!obj || typeof obj !== 'object' || depth > 3) return undefined;
        var i, k, v;
        for (i = 0; i < names.length; i++) {
            v = obj[names[i]];
            if (v != null && typeof v !== 'object') return v;
        }
        for (k in obj) {
            if (obj[k] && typeof obj[k] === 'object') {
                v = pickField(obj[k], names, depth + 1);
                if (v !== undefined) return v;
            }
        }
        return undefined;
    }

    function fmtSpeed(v) {
        if (v == null || v === '') return '';
        if (typeof v === 'number') return (v > 0 ? formatBytes(v) : '0 B') + '/s';
        var t = String(v).trim();
        if (/[KMGT]?i?B$/i.test(t)) t += '/s';          // "1.2 MB" -> "1.2 MB/s"
        return t;
    }

    // Called for every torrentstream-* WebSocket message.
    function applyTorrentFeedback(msg) {
        if (!state.activeStreamMediaId) return;           // not streaming a torrent: not ours
        var payload = msg && (msg.payload || msg.data);
        if (!payload || typeof payload !== 'object') return;

        var info = state.torrentInfo;
        if (!info) {
            info = state.torrentInfo = { bar: 0, at: 0, stage: null, speed: null, speedActive: false,
                                         pct: null, seeders: null, peers: null, size: '' };
        }
        var changed = false;

        var stage = null;
        try { stage = (JSON.stringify(payload).match(TORRENT_STAGE_RE) || [])[0] || null; } catch (e) {}
        if (stage && stage !== info.stage) { info.stage = stage; changed = true; }

        var speed = pickField(payload, ['downloadSpeed', 'download_speed', 'downSpeed', 'speed'], 0);
        if (speed !== undefined) {
            info.speed = fmtSpeed(speed);
            info.speedActive = parseFloat(info.speed) > 0;
            changed = true;
        }
        var pct = parseFloat(pickField(payload, ['progressPercentage', 'bufferedPercentage', 'percentage', 'percent'], 0));
        if (isFinite(pct)) { info.pct = Math.max(0, Math.min(100, pct)); changed = true; }
        var seeders = parseInt(pickField(payload, ['seeders', 'connectedSeeders', 'activeSeeders'], 0), 10);
        if (isFinite(seeders)) { info.seeders = seeders; changed = true; }
        var peers = parseInt(pickField(payload, ['peers', 'activePeers', 'connectedPeers'], 0), 10);
        if (isFinite(peers)) { info.peers = peers; changed = true; }
        var size = pickField(payload, ['size', 'totalSize'], 0);
        if (size !== undefined) { info.size = typeof size === 'number' ? formatBytes(size) : String(size); changed = true; }

        if (!changed) return;
        info.at = Date.now();
        renderTorrentFeedback();
    }

    // Paints the overlay (while it is up) and the buffering label (while the video stalls).
    // Also runs once a second while the overlay is up, so the waiting time keeps counting.
    function renderTorrentFeedback() {
        var overlay = $('#torrent-loading');
        var up = overlay && !overlay.classList.contains('hidden');
        var info = state.torrentInfo;
        if (up && state.transcoding) {
            // the torrent is already running; the wait is for the server's transcoder
            var tw = Math.max(0, Math.round((Date.now() - state.loadingSince) / 1000));
            setText($('#torrent-speed'), '');
            setText($('#torrent-detail'), 'Waiting ' + tw + 's');
            setText($('#torrent-hint'), tw >= 25
                ? 'The first segments can take a while on a slower server. Press RETURN to cancel.' : '');
        } else if (up && state.playbackKind === 'torrent') {
            var waited = Math.max(0, Math.round((Date.now() - state.loadingSince) / 1000));
            var st = info && info.stage ? TORRENT_STAGES[info.stage] : null;
            if (info) {
                // The bar only moves forward: stage progress first, real download progress once it is larger.
                if (st) info.bar = Math.max(info.bar, st.floor);
                if (info.pct > 0) info.bar = Math.max(info.bar, Math.min(95, info.pct));
                var fill = $('#torrent-progress-fill');
                if (fill) fill.style.width = info.bar + '%';
            }
            var status = st ? st.text
                : (info && (info.speed != null || info.seeders != null) ? 'Buffering the stream\u2026' : null);
            if (status) setText($('#torrent-loading-status'), status);

            var parts = [];
            if (info) {
                if (info.seeders != null) parts.push(info.seeders + (info.seeders === 1 ? ' seeder' : ' seeders'));
                if (info.peers != null) parts.push(info.peers + (info.peers === 1 ? ' peer' : ' peers'));
                if (info.pct != null) parts.push((Math.round(info.pct * 10) / 10) + '% downloaded');
                if (info.size) parts.push(info.size);
            }
            parts.push('Waiting ' + waited + 's');
            setText($('#torrent-speed'), info && info.speed ? '\u2193 ' + info.speed : '');
            setText($('#torrent-detail'), parts.join('  \u00b7  '));
            var slow = waited >= SLOW_START_SECONDS && !(info && info.speedActive);
            setText($('#torrent-hint'), slow
                ? 'Still looking for peers \u2014 slow torrents can take a minute or more. Press RETURN to cancel, then choose another torrent.'
                : '');
        }
        if (state.buffering) setText($('#player-buffering-text'), bufferingLabel());
    }

    var torrentWaitTimer = null;
    function startTorrentWaitTicker() {
        stopTorrentWaitTicker();
        torrentWaitTimer = setInterval(renderTorrentFeedback, 1000);
    }
    function stopTorrentWaitTicker() {
        if (torrentWaitTimer) { clearInterval(torrentWaitTimer); torrentWaitTimer = null; }
    }

    function showTorrentLoadingOverlay(title, status) {
        var el = $('#torrent-loading');
        if (!el) return;
        $('#torrent-loading-title').textContent = title || 'Preparing stream\u2026';
        $('#torrent-loading-status').textContent = status || 'Please wait';
        $('#torrent-progress-fill').style.width = '0%';
        setText($('#torrent-speed'), '');
        setText($('#torrent-detail'), '');
        setText($('#torrent-hint'), '');
        state.torrentInfo = null;
        state.loadingSince = Date.now();
        el.classList.remove('hidden');
        startTorrentWaitTicker();
    }
    function updateTorrentLoadingOverlay(status, progressPercent, speedBytes) {
        var statusEl = $('#torrent-loading-status');
        if (statusEl && status) statusEl.textContent = status;
        var fill = $('#torrent-progress-fill');
        if (fill && typeof progressPercent === 'number') fill.style.width = Math.min(100, progressPercent) + '%';
        if (speedBytes) setText($('#torrent-speed'), '\u2193 ' + fmtSpeed(speedBytes));
    }
    function hideTorrentLoadingOverlay() {
        stopTorrentWaitTicker();
        var el = $('#torrent-loading');
        if (el) el.classList.add('hidden');
    }

    // ===== AVPlay =====
    function initAVPlay() {
        if (typeof webapis === 'undefined' || !webapis.avplay) {
            console.error('AVPlay API not available.');
            return false;
        }
        return true;
    }

    function createAVPlayObject() {
        var container = $('#av-player-container');
        container.innerHTML = '';
        var obj = document.createElement('object');
        obj.id = 'av-player-object';
        obj.type = 'application/avplayer';
        obj.style.width = '100%';
        obj.style.height = '100%';
        obj.style.position = 'absolute';
        obj.style.top = '0'; obj.style.left = '0';
        container.appendChild(obj);
        return obj;
    }

    // ===== Playback helpers =====
    // Playback speeds offered in the player and in Settings. Whether a TV accepts each of them is up to
    // its AVPlay implementation; a speed it rejects falls back to 1x (see applyPlaybackSpeed).
    var SPEED_OPTIONS = [
        { v: '0.75', l: '0.75x' }, { v: '1', l: 'Normal' }, { v: '1.25', l: '1.25x' },
        { v: '1.5', l: '1.5x' }, { v: '2', l: '2x' }
    ];

    var PROGRESS_THRESHOLD = 0.8;   // mark the episode watched on AniList at 80%
    var CONTINUITY_INTERVAL = 15000;
    var toastTimer = null;

    function showToast(text, ms) {
        var el = $('#osd-toast');
        if (!el) return;
        el.textContent = text;
        el.classList.add('show');
        if (toastTimer) clearTimeout(toastTimer);
        toastTimer = setTimeout(function () { el.classList.remove('show'); }, ms || 3000);
    }

    function leavePlayer() {
        hidePlayerError();
        if (state.playbackOrigin === 'home') {
            showScreen('home');
            var b = $('#hero-play-btn');
            if (b && b.style.display !== 'none') { try { b.focus(); } catch (e) {} }
        } else {
            showScreen('detail');
            var items = document.querySelectorAll('#episode-list .episode-item');
            var idx = -1;
            (state.episodes || []).forEach(function (ep, i) {
                if ((ep.episodeNumber || ep.number || (i + 1)) === state.currentEpisodeNumber) idx = i;
            });
            if (idx >= 0 && items[idx]) { try { items[idx].focus(); } catch (e) {} }
        }
    }

    function episodeList() {
        var a = state.currentAnime;
        return (a && state.episodesMediaId === a.mediaId && state.episodes) ? state.episodes : [];
    }
    function findEpisode(n) {
        var list = episodeList();
        for (var i = 0; i < list.length; i++) {
            if ((list[i].episodeNumber || list[i].number || (i + 1)) === n) return list[i];
        }
        return null;
    }
    function getTotalEpisodes() {
        var list = episodeList(), max = 0;
        list.forEach(function (ep, i) {
            var n = ep.episodeNumber || ep.number || (i + 1);
            if (n > max) max = n;
        });
        if (max) return max;
        var a = state.currentAnime;
        return (a && a.episodes) ? a.episodes : 0;
    }
    function hasNextEpisode() {
        var total = getTotalEpisodes();
        return total > 0 && state.currentEpisodeNumber < total;
    }

    // Loads the episode list of the anime being played (needed for next/previous
    // when playback started from the home screen instead of the detail screen).
    // Episodes of an anime merged with what is on disk and the user's list data.
    // Cached for the anime currently being browsed or played.
    function mergeEpisodes(eps, entry, anime) {
        eps = (eps || []).slice();
        var local = {};
        var entryEps = (entry && entry.episodes) || [];
        entryEps.forEach(function (e) {
            if (e && e.localFile) local[e.episodeNumber] = e;
        });
        if (eps.length === 0) {
            // no episode metadata: fall back to the files on disk, then to 1..N
            eps = entryEps.slice();
            if (eps.length === 0 && anime && anime.episodes) {
                for (var n = 1; n <= anime.episodes; n++) eps.push({ episodeNumber: n });
            }
        }
        return eps.map(function (ep, i) {
            var number = ep.episodeNumber || ep.number || (i + 1);
            var le = local[number];
            if (le && !ep.localFile) {
                var copy = {};
                for (var k in ep) copy[k] = ep[k];
                copy.localFile = le.localFile;
                copy.isDownloaded = true;
                return copy;
            }
            return ep;
        });
    }

    function loadEpisodeBundle(anime, force) {
        var id = anime.mediaId;
        if (!force && state.bundle && state.bundle.mediaId === id && state.bundle.episodes.length) {
            return Promise.resolve(state.bundle);
        }
        var pEntry = api.getAnimeEntry(id).catch(function () { return null; });
        var pEps = api.getEpisodes(id).catch(function () { return []; });
        return Promise.all([pEps, pEntry]).then(function (r) {
            var episodes = mergeEpisodes(r[0], r[1], anime);
            var bundle = { mediaId: id, episodes: episodes, entry: r[1] };
            state.bundle = bundle;
            state.episodes = episodes;
            state.episodesMediaId = id;
            return bundle;
        });
    }

    function ensureEpisodes(anime) {
        return loadEpisodeBundle(anime, false).then(function (b) { return b.episodes; });
    }

    function readPlaybackPosition() {
        try {
            return {
                cur: webapis.avplay.getCurrentTime() / 1000,
                dur: webapis.avplay.getDuration() / 1000
            };
        } catch (e) { return null; }
    }

    // Save where we are so the episode can be resumed later (any device).
    function saveContinuity(pos) {
        if (!pos || !(pos.dur > 0) || pos.cur < 5 || !state.playbackMediaId) return;
        state.lastContinuitySave = Date.now();
        api.saveContinuity({
            currentTime: pos.cur,
            duration: pos.dur,
            mediaId: state.playbackMediaId,
            episodeNumber: state.currentEpisodeNumber,
            filepath: state.playbackKind === 'local' && state.lastPlayback ? (state.lastPlayback.localPath || '') : '',
            kind: 'external_player'
        });
    }

    // Marks the episode watched on AniList once enough of it has been played.
    // Never lowers existing progress (re-watching an old episode is safe).
    function maybeSyncProgress(cur, dur) {
        if (state.progressSynced || !state.playbackMediaId) return;
        if (!(dur > 0) || cur / dur < (parseFloat(getSetting('watchedAt')) || PROGRESS_THRESHOLD)) return;
        if (Date.now() < state.progressRetryAt) return;

        var mediaId = state.playbackMediaId;
        var episode = state.currentEpisodeNumber;
        var known = state.listProgress[mediaId] || 0;
        state.progressSynced = true;
        if (episode <= known) {
            DEBUG && console.log('[Progress] AniList already at episode ' + known + '; not changing it.');
            return;
        }
        api.updateEntryProgress(mediaId, episode, getTotalEpisodes()).then(function () {
            DEBUG && console.log('[Progress] Episode ' + episode + ' marked as watched.');
            state.listProgress[mediaId] = episode;
            state.needsRefresh = true;
            showToast('Episode ' + episode + ' marked as watched');
        }).catch(function (e) {
            console.warn('[Progress] update failed, will retry:', e);
            state.progressSynced = false;
            state.progressRetryAt = Date.now() + 30000;
        });
    }

    // ===== Audio & subtitle tracks =====
    var LANG_ALIASES = {
        ja: 'jpn', jp: 'jpn', jpn: 'jpn', japanese: 'jpn',
        en: 'eng', eng: 'eng', english: 'eng',
        es: 'spa', spa: 'spa', spanish: 'spa',
        fr: 'fre', fra: 'fre', fre: 'fre', french: 'fre',
        de: 'ger', deu: 'ger', ger: 'ger', german: 'ger',
        it: 'ita', ita: 'ita', italian: 'ita',
        pt: 'por', por: 'por', portuguese: 'por',
        ru: 'rus', rus: 'rus', russian: 'rus',
        ar: 'ara', ara: 'ara', arabic: 'ara',
        ko: 'kor', kor: 'kor', korean: 'kor',
        zh: 'chi', zho: 'chi', chi: 'chi', cmn: 'chi', chinese: 'chi',
        hi: 'hin', hin: 'hin', th: 'tha', tha: 'tha',
        id: 'ind', ind: 'ind', vi: 'vie', vie: 'vie',
        pl: 'pol', pol: 'pol', tr: 'tur', tur: 'tur'
    };
    var LANG_NAMES = {
        jpn: 'Japanese', eng: 'English', spa: 'Spanish', fre: 'French', ger: 'German',
        ita: 'Italian', por: 'Portuguese', rus: 'Russian', ara: 'Arabic', kor: 'Korean',
        chi: 'Chinese', hin: 'Hindi', tha: 'Thai', ind: 'Indonesian', vie: 'Vietnamese',
        pol: 'Polish', tur: 'Turkish', und: 'Unknown'
    };

    function normLang(code) {
        var c = String(code || '').toLowerCase().split(/[-_]/)[0].replace(/[^a-z]/g, '');
        if (!c) return 'und';
        return LANG_ALIASES[c] || c;
    }
    function langName(key) { return LANG_NAMES[key] || key.toUpperCase(); }

    function getPref(key, def) {
        if (!Object.prototype.hasOwnProperty.call(prefCache, key)) {
            var stored = null;
            try { stored = localStorage.getItem('seanime_pref_' + key); } catch (e) {}
            prefCache[key] = stored;
        }
        var v = prefCache[key];
        return v == null ? def : v;
    }
    function setPref(key, value) {
        prefCache[key] = String(value);
        try { localStorage.setItem('seanime_pref_' + key, value); } catch (e) {}
    }

    function channelLabel(n) {
        n = parseInt(n, 10);
        if (!n) return '';
        if (n === 1) return 'Mono';
        if (n === 2) return 'Stereo';
        if (n === 6) return '5.1';
        if (n === 8) return '7.1';
        return n + 'ch';
    }

    // Reads AVPlay's track list into { audio: [...], text: [...] }.
    // Samsung's AVPlay often reports an EMPTY language for embedded subtitles (typical for
    // ASS tracks in MKV fansubs), e.g. {"track_num":"0","track_lang":"","subtitle_type":"0","fourCC":""}.
    // Such tracks get a numbered label here; finishTracks() then tries to read the real
    // language / name from the file itself (see "Matroska header reader").
    function readTracks() {
        var all;
        try { all = webapis.avplay.getTotalTrackInfo() || []; } catch (e) { return null; }
        var audio = [], text = [];
        for (var i = 0; i < all.length; i++) {
            var t = all[i], info = {};
            try { info = JSON.parse(t.extra_info || '{}'); } catch (e) {}
            if (t.type === 'TEXT') DEBUG && console.log('[Tracks] TEXT #' + t.index + ' extra_info: ' + t.extra_info);
            var lang = normLang(info.language || info.track_lang || info.lang);
            var track = { index: t.index, lang: lang, label: langName(lang), detail: '' };
            if (t.type === 'AUDIO') {
                var parts = [];
                if (info.fourCC) parts.push(String(info.fourCC).toUpperCase());
                var ch = channelLabel(info.channels);
                if (ch) parts.push(ch);
                track.detail = parts.join(' \u00B7 ');
                if (lang === 'und') track.label = 'Audio ' + (audio.length + 1);
                audio.push(track);
            } else if (t.type === 'TEXT') {
                if (lang === 'und') track.label = 'Subtitle ' + (text.length + 1);
                if (info.fourCC) track.detail = String(info.fourCC).toUpperCase();
                text.push(track);
            }
        }
        // two tracks with the same language (e.g. full subs + signs/songs): number them
        numberDuplicateLabels(audio);
        numberDuplicateLabels(text);
        return { audio: audio, text: text };
    }

    // ----- External subtitle files (local videos) -----
    // The server lists subtitle files that sit next to a local video. They are
    // downloaded, parsed here (SRT / VTT / ASS / SSA) and drawn by the same
    // on-screen subtitle element as embedded subtitles, synced to the video time.
    var EXT_BASE = 1000;            // track index space for external subtitles
    var extSubTimer = null;
    var extSubCache = {};

    function parseStamp(str) {
        var m = /^(?:(\d+):)?(\d+):(\d+)[.,](\d+)$/.exec(String(str).replace(/^\s+|\s+$/g, ''));
        if (!m) return null;
        var frac = (m[4] + '00').slice(0, 3);
        return (((parseInt(m[1] || '0', 10) * 60 + parseInt(m[2], 10)) * 60) + parseInt(m[3], 10)) * 1000 + parseInt(frac, 10);
    }

    function stripCueMarkup(text) {
        return String(text || '')
            .replace(/\{\\[^}]*\}/g, '')            // ASS override tags
            .replace(/<[^>]+>/g, '')                // <i> <b> <font ...> and VTT voice tags
            .replace(/\\N/g, '\n').replace(/\\n/g, '\n').replace(/\\h/g, ' ')
            .replace(/^\s+|\s+$/g, '');
    }

    function parseSrtVtt(text) {
        var cues = [];
        var blocks = text.replace(/\r\n?/g, '\n').split(/\n{2,}/);
        for (var i = 0; i < blocks.length; i++) {
            var lines = blocks[i].split('\n'), t = -1;
            for (var j = 0; j < lines.length; j++) if (lines[j].indexOf('-->') >= 0) { t = j; break; }
            if (t < 0) continue;
            var parts = lines[t].split('-->');
            var start = parseStamp(parts[0]);
            var end = parseStamp(String(parts[1] || '').replace(/^\s+/, '').split(/\s+/)[0]);   // VTT cue settings follow the end time
            if (start === null || end === null) continue;
            var body = stripCueMarkup(lines.slice(t + 1).join('\n'));
            if (body) cues.push({ start: start, end: end, text: body });
        }
        return cues;
    }

    function parseAss(text) {
        var cues = [], inEvents = false, fmt = null;
        var lines = text.replace(/\r\n?/g, '\n').split('\n');
        for (var i = 0; i < lines.length; i++) {
            var line = lines[i].replace(/^\s+|\s+$/g, '');
            if (/^\[.*\]$/.test(line)) { inEvents = /^\[events\]$/i.test(line); continue; }
            if (!inEvents) continue;
            if (/^format:/i.test(line)) {
                fmt = line.slice(7).split(',').map(function (f) { return f.replace(/^\s+|\s+$/g, '').toLowerCase(); });
                continue;
            }
            if (!/^dialogue:/i.test(line) || !fmt) continue;
            var textIdx = fmt.indexOf('text'), startIdx = fmt.indexOf('start'), endIdx = fmt.indexOf('end');
            if (textIdx < 0 || startIdx < 0 || endIdx < 0) continue;
            var parts = line.slice(9).split(',');
            var raw = parts.slice(textIdx).join(',');          // the text itself may contain commas
            if (/\\p[1-9]/.test(raw)) continue;                // vector drawings (signs), not text
            var start = parseStamp(parts[startIdx]), end = parseStamp(parts[endIdx]);
            var body = stripCueMarkup(raw);
            if (start === null || end === null || !body) continue;
            cues.push({ start: start, end: end, text: body });
        }
        cues.sort(function (a, b) { return a.start - b.start; });
        return cues;
    }

    function parseSubtitles(text, type) {
        text = String(text || '').replace(/^\uFEFF/, '');
        var t = String(type || '').toLowerCase();
        if (t === 'ass' || t === 'ssa' || /^\[script info\]|^\[events\]/im.test(text)) return parseAss(text);
        return parseSrtVtt(text);
    }

    // Text of every cue visible at time `ms` (cues are sorted by start).
    function cueTextAt(cues, ms) {
        var lo = 0, hi = cues.length - 1, idx = -1;
        while (lo <= hi) {
            var mid = (lo + hi) >> 1;
            if (cues[mid].start <= ms) { idx = mid; lo = mid + 1; } else hi = mid - 1;
        }
        var out = [];
        for (var i = idx; i >= 0 && i > idx - 8; i--) {
            if (cues[i].end > ms) out.unshift(cues[i].text);
        }
        return out.join('\n');
    }

    function loadExternalSubtitle(track) {
        if (extSubCache[track.path]) return Promise.resolve(extSubCache[track.path]);
        return api.getFileText(track.path).then(function (text) {
            var cues = parseSubtitles(text, track.type);
            if (!cues.length) throw new Error('No subtitles found in ' + (track.filename || 'the file'));
            extSubCache[track.path] = cues;
            return cues;
        });
    }

    function stopExtSubs() {
        if (extSubTimer) { clearInterval(extSubTimer); extSubTimer = null; }
        state.extCues = null;
    }
    function startExtSubs(cues) {
        stopExtSubs();
        state.extCues = cues;
        extSubTimer = setInterval(tickExtSubs, 250);
        tickExtSubs();
    }
    function tickExtSubs() {
        if (!state.extCues || !state.playerReady) return;
        var pos = readPlaybackPosition();
        if (!pos) return;
        var text = cueTextAt(state.extCues, pos.cur * 1000);
        var el = $('#subtitle-text');
        if (!el || el._extText === text) return;
        el._extText = text;
        if (text) { el.textContent = text; el.style.display = 'block'; }
        else { el.textContent = ''; el.style.display = 'none'; }
    }

    function loadExternalTracks() {
        var ctx = state.lastPlayback;
        if (state.playbackKind !== 'local' || !ctx || !ctx.localPath) return Promise.resolve([]);
        return api.getLocalSubtitles(ctx.localPath).then(function (files) {
            return (files || []).map(function (f, i) {
                var lang = normLang(f.language);
                return {
                    index: EXT_BASE + i, external: true, path: f.path, type: f.type, filename: f.filename,
                    lang: lang, label: lang !== 'und' ? langName(lang) : (f.label || f.filename || 'Subtitles'),
                    detail: 'External \u00B7 ' + String(f.type || '').toUpperCase()
                };
            });
        }).catch(function (e) {
            console.warn('[Subtitles] external list failed:', e && e.message);
            return [];
        });
    }

    // ----- Matroska header reader -----
    // AVPlay does not expose subtitle names and often not the language. For local .mkv files
    // the track list (language, name, codec) sits in the first few KB of the file, so the
    // first bytes are fetched with a Range request and the "Tracks" element is read here.
    // Subtitle track N of the file is matched to AVPlay's TEXT track N (only when the counts agree).
    var containerCache = {};

    function ebmlId(b, p) {
        var first = b[p];
        if (first === undefined) return null;
        var len = 1, mask = 0x80;
        while (len <= 4 && !(first & mask)) { len++; mask >>= 1; }
        if (len > 4 || p + len > b.length) return null;
        var id = 0;
        for (var i = 0; i < len; i++) id = id * 256 + b[p + i];
        return { id: id, len: len };
    }
    function ebmlSize(b, p) {
        var first = b[p];
        if (first === undefined) return null;
        var len = 1, mask = 0x80;
        while (len <= 8 && !(first & mask)) { len++; mask >>= 1; }
        if (len > 8 || p + len > b.length) return null;
        var val = first & (mask - 1), ones = (val === mask - 1);
        for (var i = 1; i < len; i++) {
            val = val * 256 + b[p + i];
            if (b[p + i] !== 0xFF) ones = false;
        }
        return { size: ones ? -1 : val, len: len };      // -1 = unknown size
    }
    function ebmlUint(b, s, e) { var v = 0; for (var i = s; i < e; i++) v = v * 256 + b[i]; return v; }
    function ebmlStr(b, s, e) {
        var out = '';
        for (var i = s; i < e && b[i] !== 0; i++) out += String.fromCharCode(b[i]);
        return out;
    }
    function ebmlUtf8(b, s, e) {
        var bin = ebmlStr(b, s, e);
        try { return decodeURIComponent(escape(bin)); } catch (err) { return bin; }
    }

    function mkvParseEntry(b, p, end) {
        var t = {};
        while (p < end) {
            var id = ebmlId(b, p); if (!id) break;
            var sz = ebmlSize(b, p + id.len); if (!sz || sz.size < 0) break;
            var ds = p + id.len + sz.len, de = ds + sz.size;
            if (de > end) break;
            switch (id.id) {
                case 0xD7:     t.number = ebmlUint(b, ds, de); break;
                case 0x83:     t.type = ebmlUint(b, ds, de); break;
                case 0x86:     t.codec = ebmlStr(b, ds, de); break;
                case 0x22B59C: t.lang = ebmlStr(b, ds, de); break;
                case 0x22B59D: t.lang2 = ebmlStr(b, ds, de); break;
                case 0x536E:   t.name = ebmlUtf8(b, ds, de); break;
                case 0x88:     t.isDefault = ebmlUint(b, ds, de) !== 0; break;
                case 0x55AA:   t.forced = ebmlUint(b, ds, de) !== 0; break;
            }
            p = de;
        }
        return t;
    }

    // -> { tracks: { audio: [], text: [] } }, { need: bytesNeeded } when the buffer is too short, or null
    function mkvFindTracks(b) {
        var p = 0, n = b.length;
        while (p < n) {
            var id = ebmlId(b, p); if (!id) return null;
            var sz = ebmlSize(b, p + id.len); if (!sz) return null;
            var ds = p + id.len + sz.len, de = sz.size < 0 ? n : ds + sz.size;
            if (id.id === 0x18538067) { p = ds; continue; }            // Segment: read its children
            if (id.id === 0x1F43B675) return null;                      // Cluster: Tracks would have come first
            if (id.id === 0x1654AE6B) {                                 // Tracks
                if (de > n) return { need: de };
                var out = { audio: [], text: [] }, q = ds;
                while (q < de) {
                    var eid = ebmlId(b, q); if (!eid) break;
                    var esz = ebmlSize(b, q + eid.len); if (!esz || esz.size < 0) break;
                    var eds = q + eid.len + esz.len, ede = eds + esz.size;
                    if (eid.id === 0xAE) {
                        var tr = mkvParseEntry(b, eds, Math.min(ede, de));
                        if (tr.type === 17) out.text.push(tr);
                        else if (tr.type === 2) out.audio.push(tr);
                    }
                    q = ede;
                }
                return { tracks: out };
            }
            if (de > n) return { need: de + 65536 };                   // some other big element before Tracks
            p = de;
        }
        return null;
    }

    function fetchRangeBytes(url, bytes, cb) {
        var xhr = new XMLHttpRequest(), done = false;
        function end(err, data) { if (done) return; done = true; cb(err, data); }
        xhr.open('GET', url, true);
        xhr.responseType = 'arraybuffer';
        xhr.timeout = 4000;
        try { xhr.setRequestHeader('Range', 'bytes=0-' + (bytes - 1)); } catch (e) {}
        xhr.onreadystatechange = function () {
            // a server that ignores Range would send the whole (multi-GB) file: stop right away
            if (xhr.readyState === 2 && xhr.status === 200) { xhr.abort(); end(new Error('server ignores Range')); }
        };
        xhr.onload = function () {
            if (xhr.status === 206 || xhr.status === 200) end(null, new Uint8Array(xhr.response));
            else end(new Error('HTTP ' + xhr.status));
        };
        xhr.onerror = function () { end(new Error('network/CORS error')); };
        xhr.ontimeout = function () { end(new Error('timeout')); };
        xhr.send();
    }

    function loadContainerTracks(path) {
        if (containerCache[path]) return Promise.resolve(containerCache[path]);
        return new Promise(function (resolve) {
            var url = buildLocalStreamUrl(path);
            function attempt(bytes, last) {
                fetchRangeBytes(url, bytes, function (err, buf) {
                    if (err) { console.warn('[Tracks] container read failed:', err.message); resolve(null); return; }
                    if (!(buf[0] === 0x1A && buf[1] === 0x45 && buf[2] === 0xDF && buf[3] === 0xA3)) { resolve(null); return; }   // not Matroska/WebM
                    var r = mkvFindTracks(buf);
                    if (r && r.tracks) { containerCache[path] = r.tracks; resolve(r.tracks); }
                    else if (r && r.need && !last && r.need <= 24 * 1024 * 1024) attempt(r.need, true);
                    else resolve(null);
                });
            }
            attempt(1024 * 1024, false);
        });
    }

    // ----- Matroska chapters (for the skip buttons) -----
    // Chapters sit in the header next to Tracks. -> { chapters: [{start, end, title}] } (seconds),
    // { need: bytesNeeded } when the buffer is too short, or null (no chapters before the first Cluster).
    function mkvReadChapters(b, s, e) {
        var out = [];
        function atom(p, end) {
            var ch = { start: null, end: null, title: '' };
            while (p < end) {
                var id = ebmlId(b, p); if (!id) break;
                var sz = ebmlSize(b, p + id.len); if (!sz || sz.size < 0) break;
                var ds = p + id.len + sz.len, de = ds + sz.size;
                if (de > end) break;
                if (id.id === 0x91) ch.start = ebmlUint(b, ds, de) / 1e9;            // ChapterTimeStart (ns)
                else if (id.id === 0x92) ch.end = ebmlUint(b, ds, de) / 1e9;         // ChapterTimeEnd (ns)
                else if (id.id === 0x80) {                                           // ChapterDisplay
                    var q = ds;
                    while (q < de) {
                        var cid = ebmlId(b, q); if (!cid) break;
                        var csz = ebmlSize(b, q + cid.len); if (!csz || csz.size < 0) break;
                        var cds = q + cid.len + csz.len, cde = cds + csz.size;
                        if (cde > de) break;
                        if (cid.id === 0x85 && !ch.title) ch.title = ebmlUtf8(b, cds, cde);   // ChapString
                        q = cde;
                    }
                } else if (id.id === 0xB6) atom(ds, de);                             // nested ChapterAtom
                p = de;
            }
            if (ch.start != null) out.push(ch);
        }
        var p = s;
        while (p < e) {
            var id = ebmlId(b, p); if (!id) break;
            var sz = ebmlSize(b, p + id.len); if (!sz || sz.size < 0) break;
            var ds = p + id.len + sz.len, de = ds + sz.size;
            if (de > e) break;
            if (id.id === 0x45B9) {                                                  // EditionEntry
                var q = ds;
                while (q < de) {
                    var aid = ebmlId(b, q); if (!aid) break;
                    var asz = ebmlSize(b, q + aid.len); if (!asz || asz.size < 0) break;
                    var ads = q + aid.len + asz.len, ade = ads + asz.size;
                    if (ade > de) break;
                    if (aid.id === 0xB6) atom(ads, ade);                             // ChapterAtom
                    q = ade;
                }
            }
            p = de;
        }
        out.sort(function (x, y) { return x.start - y.start; });
        return out;
    }

    function mkvFindChapters(b) {
        var p = 0, n = b.length;
        while (p < n) {
            var id = ebmlId(b, p); if (!id) return null;
            var sz = ebmlSize(b, p + id.len); if (!sz) return null;
            var ds = p + id.len + sz.len, de = sz.size < 0 ? n : ds + sz.size;
            if (id.id === 0x18538067) { p = ds; continue; }            // Segment: read its children
            if (id.id === 0x1F43B675) return null;                      // Cluster: no Chapters in the header
            if (id.id === 0x1043A770) {                                 // Chapters
                if (de > n) return { need: de };
                return { chapters: mkvReadChapters(b, ds, de) };
            }
            if (de > n) return { need: de + 65536 };                   // some other big element before Chapters
            p = de;
        }
        return null;
    }

    var chapterCache = {};
    function loadContainerChapters(path) {
        if (chapterCache[path]) return Promise.resolve(chapterCache[path]);
        return new Promise(function (resolve) {
            var url;
            try { url = buildLocalStreamUrl(path); } catch (e) { resolve([]); return; }
            function attempt(bytes, last) {
                fetchRangeBytes(url, bytes, function (err, buf) {
                    if (err) { resolve([]); return; }
                    if (!(buf[0] === 0x1A && buf[1] === 0x45 && buf[2] === 0xDF && buf[3] === 0xA3)) { resolve([]); return; }   // not Matroska/WebM
                    var r = mkvFindChapters(buf);
                    if (r && r.chapters) { chapterCache[path] = r.chapters; resolve(r.chapters); }
                    else if (r && r.need && !last && r.need <= 4 * 1024 * 1024) attempt(r.need, true);
                    else resolve([]);
                });
            }
            attempt(512 * 1024, false);
        });
    }

    var MKV_CODEC_NAMES = {
        'S_TEXT/ASS': 'ASS', 'S_TEXT/SSA': 'SSA', 'S_TEXT/UTF8': 'SRT', 'S_TEXT/WEBVTT': 'VTT',
        'S_HDMV/PGS': 'PGS (image)', 'S_VOBSUB': 'VobSub (image)', 'S_DVBSUB': 'DVB (image)'
    };
    function isImageSubCodec(codec) { return /^S_(HDMV|VOBSUB|DVBSUB)/.test(codec || ''); }

    // "English [Fansub]" -> eng. Only whole words of 3+ letters, so "it" / "de" inside a name never match.
    function inferLangFromName(name) {
        var words = String(name || '').toLowerCase().split(/[^a-z]+/);
        for (var i = 0; i < words.length; i++) {
            if (words[i].length >= 3 && LANG_ALIASES[words[i]]) return LANG_ALIASES[words[i]];
        }
        return 'und';
    }

    function enrichTextTracks(embedded, mkv) {
        if (!mkv || !mkv.text.length || !embedded.length) return;
        var src = mkv.text;
        if (src.length !== embedded.length) {
            // AVPlay may leave out image-based subtitles it cannot show
            var textOnly = src.filter(function (m) { return !isImageSubCodec(m.codec); });
            if (textOnly.length === embedded.length) src = textOnly;
            else { DEBUG && console.log('[Tracks] file lists ' + src.length + ' subtitle tracks, AVPlay ' + embedded.length + ': names not matched'); return; }
        }
        embedded.forEach(function (tr, i) {
            var m = src[i];
            var lang = normLang(m.lang && m.lang !== 'und' ? m.lang : m.lang2);
            if (lang === 'und') lang = inferLangFromName(m.name);
            if (tr.lang === 'und' && lang !== 'und') tr.lang = lang;
            if (m.name) tr.label = m.name;
            else if (tr.lang !== 'und') tr.label = langName(tr.lang);
            var parts = [];
            if (m.name && tr.lang !== 'und') parts.push(langName(tr.lang));
            var codec = MKV_CODEC_NAMES[m.codec] || '';
            if (codec) parts.push(codec); else if (tr.detail) parts.push(tr.detail);
            if (m.forced) parts.push('Forced');
            if (m.isDefault) parts.push('Default');
            tr.detail = parts.join(' \u00B7 ');
        });
        DEBUG && console.log('[Tracks] subtitle names read from the file: ' + embedded.map(function (t) { return t.label + ' [' + t.lang + ']'; }).join(', '));
    }

    function numberDuplicateLabels(list) {
        var total = {}, seen = {};
        list.forEach(function (tr) { total[tr.label] = (total[tr.label] || 0) + 1; });
        list.forEach(function (tr) {
            if (total[tr.label] > 1) {
                seen[tr.label] = (seen[tr.label] || 0) + 1;
                tr.label = tr.label + ' ' + seen[tr.label];
            }
        });
        return list;
    }

    // Track info is not always available the moment playback starts, so retry briefly.
    function loadTracks(token, attempt) {
        if (token !== state.playbackToken) return;
        var tracks = readTracks();
        if (tracks && (tracks.audio.length || tracks.text.length)) {
            finishTracks(token, tracks);
        } else if (attempt < 4) {
            setTimeout(function () { loadTracks(token, attempt + 1); }, 1500);
        } else if (state.playbackKind === 'local') {
            finishTracks(token, { audio: [], text: [] });     // no embedded tracks, files next to the video may exist
        } else {
            DEBUG && console.log('[Tracks] none reported by AVPlay');
        }
    }

    function finishTracks(token, tracks) {
        var ctx = state.lastPlayback;
        var unknown = tracks.text.some(function (t) { return t.lang === 'und'; });
        var pre = Promise.resolve();
        if (unknown && state.playbackKind === 'local' && ctx && ctx.localPath) {
            pre = loadContainerTracks(ctx.localPath).then(function (mkv) {
                if (token === state.playbackToken) enrichTextTracks(tracks.text, mkv);
            }).catch(function (e) { console.warn('[Tracks] enrich failed:', e && e.message); });
        }
        pre.then(loadExternalTracks).then(function (ext) {
            if (token !== state.playbackToken) return;
            tracks.text = numberDuplicateLabels(tracks.text.concat(ext));
            state.tracks = tracks;
            DEBUG && console.log('[Tracks] audio=' + tracks.audio.length + ' subtitles=' + tracks.text.length + ' (external ' + ext.length + ')');
            applyTrackPreferences();
        });
    }

    // Returns true on success. track === null for subtitles means "off".
    function selectTrack(kind, track) {
        try {
            if (kind === 'audio') {
                webapis.avplay.setSelectTrack('AUDIO', track.index);
                state.audioIndex = track.index;
            } else {
                clearSubtitle();
                stopExtSubs();
                state.subGot = false;
                state.subWatchMs = 0;
                if (track && track.external) {
                    webapis.avplay.setSilentSubtitle(true);           // the app draws external files itself
                    state.textIndex = track.index;
                    var tk = state.playbackToken;
                    loadExternalSubtitle(track).then(function (cues) {
                        if (tk === state.playbackToken && state.textIndex === track.index) startExtSubs(cues);
                    }).catch(function (e) {
                        console.warn('[Subtitles] external load failed:', e && e.message);
                        showToast('Could not load these subtitles');
                    });
                } else if (track) {
                    // "silent" = AVPlay hands the text to the app, which draws it (styled);
                    // not silent = the TV draws the subtitles itself.
                    var native = wantNativeSubs();
                    webapis.avplay.setSilentSubtitle(!native);
                    webapis.avplay.setSelectTrack('TEXT', track.index);
                    state.textIndex = track.index;
                    state.subRender = native ? 'tv' : 'app';
                    DEBUG && console.log('[Subs] selected TEXT track ' + track.index + ' (' + track.label + '), drawn by the ' + (native ? 'TV' : 'app'));
                } else {
                    webapis.avplay.setSilentSubtitle(true);           // off: hide anything AVPlay might draw
                    state.textIndex = -1;
                }
            }
            return true;
        } catch (e) {
            console.error('[Tracks] select ' + kind + ' failed:', e);
            showToast('Could not switch ' + (kind === 'audio' ? 'audio' : 'subtitles'));
            return false;
        }
    }

    // Subtitle tracks that are not the main dialogue.
    function isSideTrack(tr) { return /sign|song|forced|karaoke|commentary/i.test(tr.label || ''); }

    // Chooses the subtitle track to start with. AVPlay reports no language for most embedded
    // subtitles, so "no language match" must not mean "no subtitles".
    function pickDefaultSubtitle(texts, subPref) {
        var i;
        if (subPref === 'off' || !texts.length) return null;
        // 1. last time the user chose a track whose language the TV does not report: same position
        if (subPref === 'und') {
            var at = parseInt(getPref('subIdx', '0'), 10) || 0;
            if (texts[at] && texts[at].lang === 'und') return texts[at];
        }
        // 2. the language the user prefers (main dialogue before signs/songs)
        for (i = 0; i < texts.length; i++) if (texts[i].lang === subPref && !isSideTrack(texts[i])) return texts[i];
        for (i = 0; i < texts.length; i++) if (texts[i].lang === subPref) return texts[i];
        // 3. language unknown: the first track that looks like the main dialogue
        var unknown = texts.filter(function (t) { return t.lang === 'und'; });
        for (i = 0; i < unknown.length; i++) if (!isSideTrack(unknown[i])) return unknown[i];
        if (unknown.length) return unknown[0];
        // 4. everything has a known, different language: do not guess
        return null;
    }

    // Uses the languages the user picked last time (defaults: Japanese audio, English subs).
    function applyTrackPreferences() {
        var t = state.tracks;
        var audioPref = getPref('audio', 'jpn');
        var subPref = getPref('sub', 'eng');
        var a = null, i;
        for (i = 0; i < t.audio.length && !a; i++) if (t.audio[i].lang === audioPref) a = t.audio[i];
        if (!a && t.audio.length) a = t.audio[0];
        if (a) selectTrack('audio', a);
        var sub = pickDefaultSubtitle(t.text, subPref);
        selectTrack('text', sub);
        var msg = [];
        if (a) msg.push('Audio: ' + a.label);
        if (sub) msg.push('Subtitles: ' + sub.label);
        if (msg.length) showToast(msg.join('   \u2022   '), 4000);

        // Some firmware ignores a track selection made in the first moments of playback: repeat it once.
        if (sub && !sub.external) {
            var tk = state.playbackToken;
            setTimeout(function () {
                if (tk !== state.playbackToken || state.textIndex !== sub.index) return;
                try {
                    webapis.avplay.setSilentSubtitle(!wantNativeSubs());
                    webapis.avplay.setSelectTrack('TEXT', sub.index);
                    DEBUG && console.log('[Subs] track selection repeated');
                } catch (e) {}
            }, 2500);
        }
    }

    // ----- Subtitle drawing -----
    // Embedded tracks are drawn in one of two ways (Settings -> Subtitle rendering):
    //   app: AVPlay stays "silent" and passes each line to onsubtitlechange; the app draws it
    //        (size / position settings, readable shadow).
    //   tv : AVPlay draws the subtitles itself. Reliable for formats whose text the TV does not
    //        hand over (some ASS tracks); the TV's own subtitle settings apply.
    // "Auto" starts with app drawing and switches to tv when no text arrives.
    var APP_SUB_TICK = 250;
    var APP_SUB_WATCH_MS = 30000;      // playing time without any subtitle text before Auto gives up on app drawing
    var appSubTimer = null;
    var lastAppTickMs = 0;

    function subModeSetting() {
        var m = getSetting('subMode');
        return (m === 'tv' || m === 'auto') ? m : 'app';
    }
    function wantNativeSubs() { return subModeSetting() === 'tv'; }

    function applySubtitleStyle() {
        var el = $('#subtitle-text');
        if (!el) return;
        el.style.fontSize = (parseInt(getSetting('subSize'), 10) || 46) + 'px';
        el.style.bottom = (parseInt(getSetting('subPos'), 10) || 150) + 'px';
    }
    function clearSubtitle() {
        state.appCues = [];
        var el = $('#subtitle-text');
        if (el) { el.textContent = ''; el.style.display = 'none'; el._extText = null; }
    }

    // ASS subtitles inside a Matroska file are handed over in the container's own line format:
    //   ReadOrder,Layer,Style,Name,MarginL,MarginR,MarginV,Effect,Text
    // (some firmware leaves out ReadOrder, or sends a whole "Dialogue:" line). Keep only the Text.
    function stripAssPayload(t) {
        var m = /^\s*Dialogue:\s*\d+,[\d:.]+,[\d:.]+,[^,]*,[^,]*,[+-]?\d+,[+-]?\d+,[+-]?\d+,[^,]*,([\s\S]*)$/i.exec(t);
        if (m) return m[1];
        m = /^\s*\d+,\d+,[^,]*,[^,]*,[+-]?\d+,[+-]?\d+,[+-]?\d+,[^,]*,([\s\S]*)$/.exec(t);
        if (m) return m[1];
        m = /^\s*\d+,[^,]*,[^,]*,[+-]?\d+,[+-]?\d+,[+-]?\d+,[^,]*,([\s\S]*)$/.exec(t);
        if (m) return m[1];
        return t;
    }
    function cleanSubtitleText(text) {
        var t = stripAssPayload(String(text == null ? '' : text));
        if (/\\p[1-9]/.test(t)) return '';                    // vector drawings (signs), not text
        return t
            .replace(/\{[^}]*\}/g, '')                        // ASS override tags and comments
            .replace(/<[^>]+>/g, '')                          // <i>, <b>, <font ...>
            .replace(/\\N/g, '\n').replace(/\\n/g, '\n').replace(/\\h/g, ' ')
            .replace(/^\s+|\s+$/g, '');
    }

    function renderAppCues() {
        var el = $('#subtitle-text');
        if (!el) return;
        var text = state.appCues.map(function (c) { return c.text; }).join('\n');
        if (el._extText === text) return;
        el._extText = text;
        if (text) { el.textContent = text; el.style.display = 'block'; }
        else { el.textContent = ''; el.style.display = 'none'; }
    }

    // Called by AVPlay for every subtitle line of the selected embedded track.
    function onSubtitleChange(duration, text, d3, d4) {
        var embeddedOn = state.textIndex >= 0 && state.textIndex < EXT_BASE;
        if (embeddedOn) {
            if (!state.subGot) {
                DEBUG && console.log('[Subs] first text from the TV: ' + JSON.stringify(String(text)).slice(0, 200) +
                            ' duration=' + duration + ' extra=' + d3 + ',' + d4);
            }
            state.subGot = true;
        }
        if (!embeddedOn || state.subRender !== 'app') return;      // off, an external file is shown, or the TV draws it
        var raw = String(text == null ? '' : text);
        var clean = cleanSubtitleText(raw);
        if (!clean) {
            if (!/\S/.test(raw)) { state.appCues = []; renderAppCues(); }   // an empty line means "clear the screen"
            return;
        }
        var pos = readPlaybackPosition();
        var now = pos ? pos.cur * 1000 : 0;
        var ms = parseInt(duration, 10);
        if (!(ms > 0)) ms = 4000;
        if (ms > 30000) ms = 30000;
        var cues = state.appCues.filter(function (c) { return c.text !== clean; });
        cues.push({ text: clean, until: now + ms });
        state.appCues = cues.slice(-3);                            // overlapping lines are shown together
        renderAppCues();
    }

    // The TV never sent any text for the selected track.
    function subtitlesNotArriving() {
        state.subWatchMs = 0;
        var mode = subModeSetting();
        console.warn('[Subs] no subtitle text received from TEXT track ' + state.textIndex + ' (rendering mode: ' + mode + ')');
        if (mode === 'auto') {
            try { webapis.avplay.setSilentSubtitle(false); } catch (e) {}
            state.subRender = 'tv';
            state.subGot = true;                                    // stop waiting
            setSetting('subMode', 'tv');                            // remember: this TV needs its own renderer
            showToast('Subtitles now drawn by the TV (Settings \u2192 Subtitle rendering)', 6000);
        } else if (mode === 'app') {
            state.subGot = true;
            showToast('No subtitle text received. Try Settings \u2192 Subtitle rendering \u2192 TV', 6000);
        }
    }

    function tickAppSubs() {
        if (!state.playerReady) return;
        var waiting = state.textIndex >= 0 && state.textIndex < EXT_BASE && state.subRender === 'app' &&
                      !state.subGot && state.isPlaying && !state.buffering;
        if (!state.appCues.length && !waiting) { lastAppTickMs = 0; return; }     // idle: leave the player alone
        var pos = readPlaybackPosition();
        if (!pos) return;
        var now = pos.cur * 1000;
        if (lastAppTickMs && Math.abs(now - lastAppTickMs) > 2500 && state.appCues.length) {
            state.appCues = [];                                     // the video jumped: drop what was on screen
            renderAppCues();
        }
        lastAppTickMs = now;
        if (state.appCues.length) {
            var keep = state.appCues.filter(function (c) { return c.until > now; });
            if (keep.length !== state.appCues.length) { state.appCues = keep; renderAppCues(); }
        }
        // waiting for the first line of the selected embedded track
        if (state.textIndex >= 0 && state.textIndex < EXT_BASE && state.subRender === 'app' &&
            !state.subGot && state.isPlaying && !state.buffering) {
            state.subWatchMs += APP_SUB_TICK;
            if (state.subWatchMs >= APP_SUB_WATCH_MS) subtitlesNotArriving();
        }
    }
    function startAppSubs() {
        stopAppSubs();
        lastAppTickMs = 0;
        appSubTimer = setInterval(tickAppSubs, APP_SUB_TICK);
    }
    function stopAppSubs() {
        if (appSubTimer) { clearInterval(appSubTimer); appSubTimer = null; }
        state.appCues = [];
    }

    // ----- Track picker panel -----
    var CHECK_SVG = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M5 12.5l4.5 4.5L19 7.5"/></svg>';

    function openTrackPanel(kind) {
        var list = kind === 'audio' ? state.tracks.audio : kind === 'speed' ? SPEED_OPTIONS : state.tracks.text;
        if (!list.length) {
            showToast(kind === 'audio' ? 'No audio tracks found' : 'No subtitles in this file');
            return;
        }
        var box = $('#track-panel-list');
        $('#track-panel-title').textContent = kind === 'audio' ? 'Audio' : kind === 'speed' ? 'Playback speed' : 'Subtitles';
        box.innerHTML = '';
        var rows = [];
        if (kind === 'text') rows.push({ track: null, label: 'Off', detail: '' });
        list.forEach(function (t) { rows.push({ track: t, label: t.label || t.l, detail: t.detail || '' }); });

        var focusEl = null;
        rows.forEach(function (r) {
            var item = document.createElement('div');
            item.className = 'track-item';
            item.tabIndex = 0;
            var isCurrent = kind === 'speed'
                ? r.track.v === String(getSetting('speed'))
                : kind === 'audio'
                ? (r.track && r.track.index === state.audioIndex)
                : (r.track ? r.track.index === state.textIndex : state.textIndex === -1);
            var name = document.createElement('span');
            name.className = 'track-name';
            name.textContent = r.label;
            var detail = document.createElement('span');
            detail.className = 'track-detail';
            detail.textContent = r.detail;
            var check = document.createElement('span');
            check.className = 'track-check';
            if (isCurrent) { check.innerHTML = CHECK_SVG; item.className += ' current'; }
            item.appendChild(name); item.appendChild(detail); item.appendChild(check);
            item.addEventListener('click', function () { chooseTrack(kind, r.track); });
            box.appendChild(item);
            if (isCurrent || !focusEl) focusEl = item;   // current row wins, else first row
        });

        state.trackPanelKind = kind;
        hideControls();
        $('#track-panel').classList.remove('hidden');
        if (focusEl) { try { focusEl.focus(); } catch (e) {} }
    }

    function closeTrackPanel(silent) {
        var kind = state.trackPanelKind;
        state.trackPanelKind = null;
        var panel = $('#track-panel');
        if (panel) panel.classList.add('hidden');
        if (silent || !kind) return;
        showControls();
        var opener = $(kind === 'audio' ? '#ctrl-audio' : kind === 'speed' ? '#ctrl-speed' : '#ctrl-subs');
        if (opener) { try { opener.focus(); } catch (e) {} }
    }

    function moveTrackFocus(delta) {
        var items = document.querySelectorAll('#track-panel-list .track-item');
        var idx = -1;
        for (var i = 0; i < items.length; i++) if (items[i] === document.activeElement) idx = i;
        var next = Math.max(0, Math.min(items.length - 1, (idx < 0 ? 0 : idx + delta)));
        if (items[next]) items[next].focus();
    }

    function chooseTrack(kind, track) {
        if (kind === 'speed') {
            setSetting('speed', track.v);
            applyPlaybackSpeed(true);
            closeTrackPanel();
            return;
        }
        if (selectTrack(kind, track)) {
            setPref(kind === 'audio' ? 'audio' : 'sub', track ? track.lang : 'off');
            if (kind === 'text' && track && track.lang === 'und') {
                var at = state.tracks.text.indexOf(track);
                if (at >= 0) setPref('subIdx', String(at));
            }
            showToast((kind === 'audio' ? 'Audio: ' : 'Subtitles: ') + (track ? track.label : 'Off') +
                      (kind === 'text' && track && !track.external && state.subRender === 'tv' ? '  (TV)' : ''));
        }
        closeTrackPanel();
    }

    // ===== Playback errors =====
    function describeTorrentError(err) {
        var m = (err && err.message) || String(err);
        var low = m.toLowerCase();
        var raw = '\n\nServer message: ' + m;
        if (/http 429|too many/.test(low)) {
            return { title: 'Too many attempts', message: 'The server is limiting requests from this TV. Wait a few minutes and try again.', canRetry: true };
        }
        if (/http 401|http 403|unauthenticated/.test(low)) {
            return { title: 'Not signed in', message: 'The server rejected the saved login. Sign in again from the start screen.', canRetry: false };
        }
        if (/disabled/.test(low)) {
            return { title: 'Torrent streaming is turned off', message: 'Enable torrent streaming and choose a torrent client in the Seanime settings.' + raw, canRetry: false };
        }
        if (/no torrent|no result|not found|no suitable|could not find/.test(low)) {
            return { title: 'No torrents found', message: 'Seanime could not find a torrent for this episode. Check that a torrent provider is installed (Extensions) and your preferred resolution in the Seanime settings, or try another episode.' + raw, canRetry: true };
        }
        if (/timed out waiting|timeout/.test(low)) {
            return { title: 'The stream took too long to start', message: 'The torrent did not become ready in time. It may have few or no seeders. Try again or pick another episode.', canRetry: true };
        }
        if (/websocket|client identity|\/events/.test(low)) {
            return { title: 'Live connection failed', message: 'The TV could not open the live-events connection that delivers the stream. Use Settings \u2192 Test connection to see what fails.', canRetry: true };
        }
        if (/failed to fetch|networkerror|network request failed|typeerror/.test(low)) {
            return { title: 'Server unreachable', message: 'Could not reach the server. Check your network and that Seanime is running.', canRetry: true };
        }
        return { title: 'Could not start the stream', message: m, canRetry: true };
    }

    function describeLocalError(err) {
        var m = (err && err.message) || String(err);
        return { title: 'Cannot open this file', message: m, canRetry: true };
    }

    var AV_ERRORS = [
        { key: 'CONNECTION_FAILED', title: 'Connection problem', fatal: true, recoverable: true, canRetry: true,
          message: 'The stream was interrupted because the connection to the server was lost. Check the network and that Seanime is running.' },
        { key: 'INVALID_URI', title: 'Invalid stream address', fatal: true, canRetry: true,
          message: 'The player rejected the stream address.' },
        { key: 'NOT_SUPPORTED_FILE', title: 'Unsupported file', fatal: true, canRetry: false,
          message: 'This TV cannot play this file format.' },
        { key: 'NOT_SUPPORTED_VIDEO_CODEC', title: 'Unsupported video format', fatal: true, canRetry: false,
          message: 'This TV cannot decode the video (for example 10-bit HEVC or AV1 on older models). Try a different release, ideally H.264.' },
        { key: 'NOT_SUPPORTED_VIDEO_RESOLUTION', title: 'Unsupported resolution', fatal: true, canRetry: false,
          message: 'This TV cannot play the video at this resolution. Try a different release.' },
        { key: 'NOT_SUPPORTED_AUDIO_CODEC', title: 'Unsupported audio', fatal: false,
          message: 'This TV cannot play this audio track. Open the audio menu and choose another track.' },
        { key: 'SEEK_FAILED', title: 'Seek failed', fatal: false,
          message: 'Cannot jump there yet \u2014 that part is not available.' },
        { key: 'NO_SPACE', title: 'Not enough space', fatal: true, canRetry: false,
          message: 'The TV ran out of storage space for the stream.' }
    ];

    // AVPlay reports errors as strings (onerror) or as exception objects (prepareAsync / open).
    function avErrorText(e) {
        if (e == null) return '';
        if (typeof e === 'string') return e;
        var parts = [];
        if (e.name) parts.push(e.name);
        if (e.type) parts.push(e.type);
        if (e.message) parts.push(e.message);
        return parts.length ? parts.join(' ') : String(e);
    }

    // The TV cannot decode this video (codec, container or size): a transcode can fix all three.
    var CODEC_FAILURE_RE = /NOT_SUPPORTED_(VIDEO_CODEC|FILE|VIDEO_RESOLUTION)/i;
    function isCodecFailure(code) { return CODEC_FAILURE_RE.test(String(code || '')); }
    // Tizen 4 reports an undecodable AV1 / 10-bit HEVC file from prepareAsync as a bare
    // {code: 0, message: 'Unknown error'} with no codec name. So a prepare failure that matches none of
    // the known causes (connection lost, bad URI, no space...) is treated as a probable decode failure.
    function isUnexplainedAvError(code) {
        var c = String(code || '').toUpperCase();
        for (var i = 0; i < AV_ERRORS.length; i++) if (c.indexOf(AV_ERRORS[i].key) >= 0) return false;
        return true;
    }
    function transcodeEnabled() { return getSetting('transcode') !== 'off'; }

    function describeTranscodeError(err) {
        var m = (err && err.message) || String(err);
        var low = m.toLowerCase();
        var raw = '\n\nServer message: ' + m;
        var src = state.lastPlayback && state.lastPlayback.kind === 'torrent' ? ' of a torrent stream' : '';
        if (/http 401|http 403|unauthenticated/.test(low)) {
            return { title: 'Not signed in', message: 'The server rejected the saved login. Sign in again from the start screen.', canRetry: false };
        }
        if (/http 404|http 405/.test(low)) {
            return { title: 'Transcoding is not available', message: 'This server does not offer media-stream transcoding. Check that your Seanime version supports it.' + raw, canRetry: false };
        }
        if (/failed to fetch|networkerror|network request failed|typeerror/.test(low)) {
            return { title: 'Server unreachable', message: 'Could not reach the server to start the transcode.', canRetry: true };
        }
        var lead = state.lastPlayback && state.lastPlayback.guessedCodec
            ? 'The TV could not open this video (it gave no reason, which usually means an unsupported codec such as AV1), and the server could not convert it'
            : 'The TV cannot decode this video, and the server could not convert it';
        return { title: 'Could not transcode this video',
                 message: lead + src + '. Check that ffmpeg is installed and transcoding is enabled in the Seanime settings, or choose a different release.' + raw,
                 canRetry: true };
    }

    function describeAvError(code, atPrepare) {
        var c = String(code || '').toUpperCase();
        for (var i = 0; i < AV_ERRORS.length; i++) {
            if (c.indexOf(AV_ERRORS[i].key) >= 0) {
                var e = AV_ERRORS[i];
                var msg = e.message;
                if (CODEC_FAILURE_RE.test(e.key)) {
                    if (state.lastPlayback && state.lastPlayback.transcode) {
                        msg = 'The TV could not play the transcoded stream either. Try a different release.';
                    } else if (!transcodeEnabled()) {
                        msg += ' Turn on \u201cTranscode unsupported video\u201d in Settings to let the server convert it.';
                    }
                }
                if (e.key === 'CONNECTION_FAILED' && atPrepare && state.playbackKind === 'local') {
                    msg = 'The TV could not open the file. It may have been moved or deleted, its drive may be offline, or the server is unreachable.';
                } else if (e.key === 'CONNECTION_FAILED' && atPrepare) {
                    msg = 'The TV could not open the stream. The torrent may have stopped or the server is unreachable.';
                }
                return { title: e.title, message: msg, canRetry: e.canRetry !== false, fatal: e.fatal !== false, recoverable: !!e.recoverable };
            }
        }
        return { title: 'Playback error', message: 'The player reported: ' + (code || 'unknown error'), canRetry: true, fatal: true, recoverable: false };
    }

    function copyCtx(ctx) {
        var o = {};
        for (var k in ctx) o[k] = ctx[k];
        return o;
    }

    function bufferingLabel() {
        var t = state.bufferingPercent > 0 ? 'Buffering\u2026 ' + Math.round(state.bufferingPercent) + '%' : 'Buffering\u2026';
        var info = state.torrentInfo;
        if (state.playbackKind === 'torrent' && info && Date.now() - info.at < 8000) {
            var bits = [];
            if (info.speed) bits.push(info.speed);
            if (info.seeders != null) bits.push(info.seeders + (info.seeders === 1 ? ' seeder' : ' seeders'));
            if (bits.length) t += '  \u00b7  ' + bits.join('  \u00b7  ');
        }
        return t;
    }

    function showBuffering(on, percent) {
        var el = $('#player-buffering');
        if (!el) return;
        if (on) {
            if (!state.buffering) { state.buffering = true; state.bufferingSince = Date.now(); }
            state.bufferingPercent = percent > 0 ? percent : 0;
            $('#player-buffering-text').textContent = bufferingLabel();
            el.classList.remove('hidden');
        } else {
            state.buffering = false;
            el.classList.add('hidden');
        }
    }
    function hideBuffering() { showBuffering(false); }

    function hidePlayerError() {
        state.playerError = null;
        var el = $('#player-error');
        if (el) el.classList.add('hidden');
    }

    function renderPlayerError(info) {
        state.playerError = info;
        state.playerErrorInfo = info;
        $('#player-error-title').textContent = info.title;
        $('#player-error-msg').textContent = info.message;
        var retry = $('#player-error-retry'), pick = $('#player-error-pick');
        var canRetry = info.canRetry !== false && !!state.lastPlayback;
        var canPick = canRetry && state.lastPlayback.kind === 'torrent';
        retry.style.display = canRetry ? '' : 'none';
        pick.style.display = canPick ? '' : 'none';
        $('#player-error').classList.remove('hidden');
        try { (canRetry ? retry : $('#player-error-back')).focus(); } catch (e) {}
    }

    // Stops playback and shows the error dialog (Try again / Choose torrent / Back).
    function failPlayback(info) {
        var pos = state.playerReady ? readPlaybackPosition() : null;
        if (state.lastPlayback && pos && pos.cur > 5) state.lastPlayback.resumeSeconds = pos.cur;
        if (state.lastPlayback) state.lastPlayback.reuseSource = false;   // stopPlayback() ends the torrent below
        stopPlayback();
        hideBuffering();
        renderPlayerError(info);
    }

    function retryPlayback() {
        var ctx = state.lastPlayback;
        hidePlayerError();
        if (!ctx) { leavePlayer(); return; }
        var next = copyCtx(ctx);
        next.isRetry = true;          // keeps resumeSeconds from where it failed
        startPlayback(next);
    }

    // Silent recovery from a dropped connection: restart at the same position.
    function recoverPlayback() {
        var ctx = state.lastPlayback;
        if (!ctx) return;
        var pos = readPlaybackPosition();
        var resume = pos && pos.cur > 5 ? pos.cur : (ctx.resumeSeconds || 0);
        var label = (state.currentAnime ? state.currentAnime.title : '') + ' \u2014 Episode ' + state.currentEpisodeNumber;
        stopPlayback();
        showTorrentLoadingOverlay(label, 'Reconnecting\u2026');
        var token = state.playbackToken;
        setTimeout(function () {
            if (token !== state.playbackToken) return;     // the user left meanwhile
            var next = copyCtx(ctx);
            next.resumeSeconds = resume;
            next.isRetry = true;
            startPlayback(next);
        }, 2000);
    }

    // The TV could not decode the video: restart the same episode, at the same position, through the
    // server's transcoder. A torrent session is kept alive and its stream URL is what gets transcoded.
    // Returns true when the switch started (the caller then stops handling the error).
        function tryTranscodeFallback(code, atPrepare) {
        var ctx = state.lastPlayback;
        // FIX: Seanime /mediastream/request can ONLY transcode local files on disk
        // like /media/anime/...mkv - it can NEVER transcode a 
        // http://.../torrentstream/stream/... URL. That always gives 500
        // "no such file or directory". For torrents, don't transcode.
        if (ctx && ctx.kind === 'torrent') {
            console.warn('[Transcode] Torrent cannot be transcoded, will show Choose torrent instead');
            return false;
        }
        var explicit = isCodecFailure(code);
        if (!ctx || ctx.transcode || !transcodeEnabled()) return false;
        if (!explicit && !(atPrepare && isUnexplainedAvError(code))) return false;
        var pos = state.playerReady ? readPlaybackPosition() : null;
        var next = copyCtx(ctx);
        next.transcode = true;
        next.guessedCodec = !explicit;            // AVPlay gave no reason; transcoding is a best guess
        next.reuseSource = ctx.kind === 'torrent';
        next.resumeSeconds = pos && pos.cur > 5 ? pos.cur : (ctx.resumeSeconds || 0);
        next.isRetry = true;
        console.warn('[Transcode] ' + (explicit ? 'TV cannot decode this video' : 'TV could not open this video (no reason given)') +
            ' (' + (code || 'no error text') + '); switching to server transcoding');
        stopPlayback(true);                      // true: keep the torrent session running
        showToast(explicit ? 'This TV cannot decode this video. Transcoding on the server\u2026'
                           : 'This TV could not play this video. Trying server transcoding\u2026', 5000);
        startPlayback(next);
        return true;
    }

    function onAvError(type) {
        console.error('[AVPlay] error:', type);
        if (tryTranscodeFallback(type)) return;
        var info = describeAvError(type, false);
        if (!info.fatal) { showToast(info.message, 5000); return; }
        if (info.recoverable && state.autoRetries < 2 && state.lastPlayback) {
            state.autoRetries++;
            showToast('Connection lost. Reconnecting\u2026', 4000);
            recoverPlayback();
            return;
        }
        failPlayback(info);
    }

    // ===== Transcoding =====
    // Asks Seanime's media streaming to transcode `sourceUrl` (torrent stream) or the library file in
    // ctx.localPath, and resolves with the HLS playlist URL AVPlay should open.
    var TRANSCODE_MASTER = '/mediastream/transcode/master.m3u8';

    function requestTranscodeUrl(ctx, sourceUrl) {
        var path = ctx.kind === 'local' ? ctx.localPath : sourceUrl;
        if (!path) return Promise.reject(new Error('Nothing to transcode'));
        var body = {
            path: path,
            streamType: 'transcode',
            audioStreamIndex: 0,
            clientId: getServerClientId() || getClientId()
        };
        DEBUG && console.log('[Transcode] POST /mediastream/request', ctx.kind === 'local' ? path : maskToken(path));
        return api.request('/mediastream/request', { method: 'POST', body: JSON.stringify(body) }).then(function (data) {
            var c = unwrapData(data) || {};
            var u = typeof c.streamUrl === 'string' && c.streamUrl ? c.streamUrl : CONFIG.apiPath + TRANSCODE_MASTER;
            // never fall back to the original file: the TV just proved it cannot decode it
            if (/\/mediastream\/direct/.test(u)) u = CONFIG.apiPath + TRANSCODE_MASTER;
            u = rewriteStreamUrl(u);                       // fills {{SCHEME}}/{{HOST}} placeholders first
            if (!/^https?:/i.test(u)) u = CONFIG.serverUrl + (u.charAt(0) === '/' ? '' : '/') + u;
            // AVPlay cannot send the auth header: carry the signed token in the URL like local files do
            if (CONFIG.passwordHash && !/[?&]token=/.test(u)) {
                var endpoint = u.replace(/^https?:\/\/[^\/]+/i, '').split('?')[0];
                u += (u.indexOf('?') < 0 ? '?' : '&') + 'token=' + encodeURIComponent(makeHmacToken(endpoint));
            }
            DEBUG && console.log('[Transcode] playlist:', maskToken(u));
            return u;
        });
    }

    // ===== Core Playback =====
    function maskToken(url) { return String(url).replace(/([?&]token=)[^&]+/, '$1***'); }

    // Torrents are never chosen automatically: selecting an episode opens the picker, and
    // playback only starts once the user has picked a torrent (startManualTorrent).
    function startTorrentPlayback(anime, episodeNumber, aniDbEpisode) {
        state.currentAnime = anime;
        openTorrentPicker(anime, episodeNumber, aniDbEpisode, false);
    }
    function startLocalPlayback(anime, episodeNumber, path) {
        startPlayback({ kind: 'local', anime: anime, episodeNumber: episodeNumber, localPath: path });
    }

    // Plays an episode from disk when the file exists (and the setting allows), otherwise streams it.
    function playEpisodeAuto(anime, episodeNumber, epInfo) {
        var path = epInfo && epInfo.localFile && epInfo.localFile.path;
        if (path && getSetting('preferLocal') !== 'off') {
            startLocalPlayback(anime, episodeNumber, path);
        } else {
            startTorrentPlayback(anime, episodeNumber, (epInfo && epInfo.aniDBEpisode) || (epInfo && epInfo.aniDb) || null);
        }
    }

    function startPlayback(ctx) {
        var anime = ctx.anime, episodeNumber = ctx.episodeNumber;
        if (!anime || !anime.mediaId) {
            showAppToast('Missing anime information.');
            return;
        }

        hidePlayerError();
        hideBuffering();
        cancelUpNext();
        var token = ++state.playbackToken;
        if (!ctx.isRetry) state.autoRetries = 0;
        state.lastPlayback = ctx;
        state.playbackKind = ctx.kind;
        state.currentAnime = anime;
        state.currentEpisodeNumber = episodeNumber;
        state.playbackMediaId = anime.mediaId;
        state.progressSynced = false;
        state.progressRetryAt = 0;
        state.lastContinuitySave = Date.now();
        state.activeStreamMediaId = ctx.kind === 'torrent' ? anime.mediaId : null;
        state.activeStreamEpisode = ctx.kind === 'torrent' ? episodeNumber : null;
        state.activeSessionId = null;
        state.transcoding = !!ctx.transcode;
        state.tracks = { audio: [], text: [] };
        state.audioIndex = null;
        state.textIndex = -1;
        clearSubtitle();
        applySubtitleStyle();
        state.osdProgress = { pct: '0%', cur: '00:00', total: '00:00' };
        paintProgress();

        showScreen('player');
        var label = anime.title + ' \u2014 Episode ' + episodeNumber;
        $('#player-title').textContent = label;
        showTorrentLoadingOverlay(label, ctx.transcode ? 'Starting transcoder\u2026'
            : (ctx.kind === 'local' ? 'Opening file\u2026' : 'Connecting\u2026'));

        ensureEpisodes(anime).catch(function () {});

        cancelScrub(true);
        state.lastSeek = null;
        state.speedApplied = false;
        updateSpeedButton();
        loadSkipSegments(ctx, token);

        // Where to resume: after a failure, where it stopped; otherwise the saved position
        var resumePromise = ctx.resumeSeconds > 0
            ? Promise.resolve(ctx.resumeSeconds)
            : api.getContinuityItem(anime.mediaId).then(function (item) {
                if (getSetting('resume') !== 'off' && item && item.episodeNumber === episodeNumber && item.duration > 0 &&
                    item.currentTime > 15 && item.currentTime / item.duration < 0.9) {
                    return item.currentTime;
                }
                return 0;
            });

        var urlPromise;
        if (ctx.kind === 'local') {
            try { urlPromise = Promise.resolve(buildLocalStreamUrl(ctx.localPath)); }
            catch (e) { urlPromise = Promise.reject(e); }
        } else if (ctx.reuseSource && ctx.sourceUrl) {
            urlPromise = Promise.resolve(ctx.sourceUrl);     // the torrent is already running: transcode its stream
        } else {
            urlPromise = connectWebSocket()
                .then(function () { return waitForClientIdentity(8000); })
                .then(function () {
                    if (token !== state.playbackToken) return null;
                    updateTorrentLoadingOverlay('Searching for torrent\u2026');
                    var urlWait = waitForStreamUrl(90000);
                    urlWait.catch(function () {});     // no unhandled rejection if the start call fails first
                    return api.startTorrentStream(anime.mediaId, episodeNumber, ctx.aniDb, { torrent: ctx.torrent, fileIndex: ctx.fileIndex })
                        .then(function () { return urlWait; });
                });
        }

        urlPromise.then(function (streamUrl) {
            if (!streamUrl || token !== state.playbackToken) return;
            if (ctx.kind === 'torrent') ctx.sourceUrl = streamUrl;      // lets a codec failure reuse the live stream
            if (!ctx.transcode) { openStream(streamUrl, token, resumePromise); return; }
            return requestTranscodeUrl(ctx, streamUrl).then(function (playlistUrl) {
                if (token !== state.playbackToken) return;
                openStream(playlistUrl, token, resumePromise);
            }, function (error) {
                if (token !== state.playbackToken) return;
                console.error('[Transcode] request failed:', error);
                failPlayback(describeTranscodeError(error));
            });
        }).catch(function (error) {
            if (token !== state.playbackToken) return;     // the user already left
            console.error('[Playback] Start failed:', error);
            failPlayback(ctx.kind === 'local' ? describeLocalError(error) : describeTorrentError(error));
        });
    }

    function openStream(streamUrl, token, resumePromise) {
        DEBUG && console.log('[Playback] Playing stream URL:', maskToken(streamUrl));
        hideTorrentLoadingOverlay();
        if (!initAVPlay()) {
            failPlayback({ title: 'Player unavailable', message: 'AVPlay is not available on this device.', canRetry: false });
            return;
        }
        try {
            createAVPlayObject();
            webapis.avplay.open(streamUrl);
            state.avplayOpen = true;
            webapis.avplay.setDisplayRect(0, 0, 1920, 1080);
            webapis.avplay.setListener({
                onstreamcompleted: function () { if (token === state.playbackToken) onStreamCompleted(); },
                onsubtitlechange: function (duration, text, d3, d4) { if (token === state.playbackToken) onSubtitleChange(duration, text, d3, d4); },
                onbufferingstart: function () { if (token === state.playbackToken) showBuffering(true, 0); },
                onbufferingprogress: function (percent) { if (token === state.playbackToken) showBuffering(true, percent); },
                onbufferingcomplete: function () { if (token === state.playbackToken) hideBuffering(); },
                onerror: function (type) { if (token === state.playbackToken) onAvError(type); }
            });
            webapis.avplay.prepareAsync(function () {
                if (token !== state.playbackToken) return;
                state.playerReady = true;
                var begin = function () {
                    if (token !== state.playbackToken) return;
                    try { webapis.avplay.play(); } catch (e) {}
                    state.isPlaying = true;
                    updatePlayPauseButton();
                    startProgressTracking();
                    showControls();
                    loadTracks(token, 0);
                    startAppSubs();
                    applyPlaybackSpeed(true);
                };
                resumePromise.then(function (sec) {
                    if (!(sec > 0)) { begin(); return; }
                    try {
                        webapis.avplay.seekTo(Math.floor(sec * 1000), function () {
                            showToast('Resumed from ' + formatTime(sec));
                            begin();
                        }, function () { begin(); });
                    } catch (e) { begin(); }
                });
            }, function (error) {
                if (token !== state.playbackToken) return;
                console.error('[AVPlay] Prepare error:', error);
                var text = avErrorText(error);
                if (tryTranscodeFallback(text, true)) return;
                failPlayback(describeAvError(text, true));
            });
        } catch (e) {
            console.error('[AVPlay] open failed:', e);
            var errText = avErrorText(e);
            if (tryTranscodeFallback(errText, true)) return;
            failPlayback(describeAvError(errText, true));
        }
    }

    // Previous / next episode (delta = -1 / +1)
    function playRelativeEpisode(delta) {
        var anime = state.currentAnime;
        if (!anime) return;
        var target = state.currentEpisodeNumber + delta;
        var total = getTotalEpisodes();
        if (target < 1) { showToast('This is the first episode'); return; }
        if (total && target > total) { showToast('This is the last episode'); return; }
        cancelUpNext();
        var info = findEpisode(target);
        stopPlayback().then(function () {
            playEpisodeAuto(anime, target, info);
        });
    }

    // End of episode: sync progress, then offer the next episode.
    function onStreamCompleted() {
        DEBUG && console.log('[AVPlay] Stream completed');
        state.isPlaying = false;
        updatePlayPauseButton();
        maybeSyncProgress(1, 1);
        if (hasNextEpisode()) {
            showUpNext(state.currentEpisodeNumber + 1);
        } else {
            stopPlayback();
            leavePlayer();
        }
    }

    function showUpNext(n) {
        cancelUpNext();
        hideControls();
        var el = $('#up-next');
        if (!el) return;
        var info = findEpisode(n);
        var epTitle = info && info.episodeTitle ? ' \u2014 ' + info.episodeTitle : '';
        $('#up-next-title').textContent = 'Episode ' + n + epTitle;
        var remaining = 10;
        var auto = getSetting('autoNext') !== 'off';
        $('#up-next-count').textContent = auto ? 'Starting in ' + remaining + 's' : 'Press OK to play it now';
        el.classList.remove('hidden');
        state.upNext = {
            timer: auto ? setInterval(function () {
                remaining--;
                if (remaining <= 0) { playRelativeEpisode(1); return; }
                $('#up-next-count').textContent = 'Starting in ' + remaining + 's';
            }, 1000) : null
        };
    }

    function cancelUpNext() {
        if (state.upNext) { if (state.upNext.timer) clearInterval(state.upNext.timer); state.upNext = null; }
        var el = $('#up-next');
        if (el) el.classList.add('hidden');
    }

    function avplayPlay() {
        if (!state.playerReady) return;
        try { webapis.avplay.play(); state.isPlaying = true; updatePlayPauseButton(); } catch (e) {}
    }
    function avplayPause() {
        if (!state.playerReady) return;
        try { webapis.avplay.pause(); state.isPlaying = false; updatePlayPauseButton(); } catch (e) {}
        saveContinuity(readPlaybackPosition());
    }
    function avplaySeekRelative(ms) {
        if (!state.playerReady) return;
        clearSubtitle();
        try {
            if (ms >= 0) webapis.avplay.jumpForward(ms, function () {}, function () {});
            else webapis.avplay.jumpBackward(Math.abs(ms), function () {}, function () {});
        } catch (e) {}
    }
    // ----- Seeking to any position: scrub mode -----
    // UP from the buttons focuses the progress bar; with the OSD hidden, LEFT/RIGHT (and the remote's
    // REWIND/FORWARD) start scrubbing too. A press moves a pending target that is drawn on the bar:
    // seeking on every press would be slow on a torrent stream. Holding a key accelerates through the
    // SCRUB_TIERS (10 s, then 30 s, then 1 min). The seek happens when the keys stop (SCRUB_COMMIT_DELAY),
    // or at once on OK. BACK cancels. Tune the numbers here:
    var SCRUB_TIERS = [{ after: 0, sec: 10 }, { after: 1500, sec: 30 }, { after: 3500, sec: 60 }];
    var SCRUB_STEP_INTERVAL = 280;     // ms between steps while a key is held (key repeat is faster than this)
    var SCRUB_STREAK_GAP = 650;        // presses closer together than this count as one hold (> the TV's first-repeat delay)
    var SCRUB_COMMIT_DELAY = 800;      // ms after the last press until the seek is made

    function seekAbsolute(ms) {
        if (!state.playerReady) return;
        ms = Math.max(0, Math.round(ms));
        state.lastSeek = { ms: ms, at: Date.now() };
        clearSubtitle();
        try {
            webapis.avplay.seekTo(ms, function () {}, function () { showToast('Cannot jump there yet'); });
        } catch (e) { showToast('Cannot jump there yet'); return; }
        var pos = readPlaybackPosition();
        if (pos && pos.dur > 0) updateProgressUI(ms / 1000, pos.dur);     // OSD follows at once
    }

    function scrubTierSeconds(heldMs) {
        var sec = SCRUB_TIERS[0].sec;
        for (var i = 0; i < SCRUB_TIERS.length; i++) if (heldMs >= SCRUB_TIERS[i].after) sec = SCRUB_TIERS[i].sec;
        return sec;
    }

    function paintScrub() {
        var s = state.scrub;
        if (!s) return;
        var ghost = $('#progress-ghost'), label = $('#progress-ghost-time');
        if (ghost) ghost.style.left = (s.target / s.dur * 100) + '%';
        if (label) {
            var delta = (s.target - s.from) / 1000;
            label.textContent = formatTime(s.target / 1000) + '   ' + (delta < 0 ? '\u2212' : '+') + formatTime(Math.abs(delta));
        }
    }

    function armScrubCommit() {
        var s = state.scrub;
        if (!s) return;
        if (s.timer) clearTimeout(s.timer);
        s.timer = setTimeout(commitScrub, SCRUB_COMMIT_DELAY);
    }

    // dir: -1 / +1. Called for every key press (including the TV's key repeat).
    function scrubStep(dir) {
        if (!state.playerReady) return;
        var now = Date.now(), s = state.scrub;
        if (!s) {
            var pos = readPlaybackPosition();
            if (!pos || !(pos.dur > 0)) return;
            var from = pos.cur * 1000;
            // just after a seek the TV still reports the old time: trust the seek target
            if (state.lastSeek && now - state.lastSeek.at < 2500) from = state.lastSeek.ms;
            s = state.scrub = { from: from, target: from, dur: pos.dur * 1000, dir: 0,
                                streakStart: now, lastKey: 0, lastStep: 0, timer: null };
            showControls();
            var bar = $('#progress-bar');
            if (bar) { bar.classList.add('scrubbing'); try { bar.focus(); } catch (e) {} }
        }
        if (dir !== s.dir || now - s.lastKey > SCRUB_STREAK_GAP) { s.dir = dir; s.streakStart = now; s.lastStep = 0; }
        s.lastKey = now;
        armScrubCommit();                                  // every press (even a throttled one) postpones the seek
        if (now - s.lastStep < SCRUB_STEP_INTERVAL) return;
        s.lastStep = now;
        var step = scrubTierSeconds(now - s.streakStart) * 1000;
        s.target = Math.max(0, Math.min(Math.max(0, s.dur - 2000), s.target + dir * step));
        paintScrub();
    }

    function cancelScrub(silent) {
        var s = state.scrub;
        if (!s) return;
        if (s.timer) clearTimeout(s.timer);
        state.scrub = null;
        var bar = $('#progress-bar');
        if (bar) bar.classList.remove('scrubbing');
        if (!silent && controlsShown()) showControls();
    }

    function commitScrub() {
        var s = state.scrub;
        if (!s) return;
        var target = s.target, moved = Math.abs(target - s.from) >= 1000;
        cancelScrub(true);
        if (moved) seekAbsolute(target);
        if (controlsShown()) showControls();
    }

    // ----- Playback speed -----
    function speedLabel(v) { return (parseFloat(v) || 1) + 'x'; }

    function updateSpeedButton() {
        var btn = $('#ctrl-speed');
        if (!btn) return;
        var t = speedLabel(getSetting('speed'));
        var size = t.length <= 2 ? 12 : (t.length <= 4 ? 9.5 : 8);
        btn.innerHTML = '<svg viewBox="0 0 24 24" fill="currentColor" aria-hidden="true"><text x="12" y="' + (size > 10 ? 16 : 15) +
            '" text-anchor="middle" font-size="' + size + '" font-weight="800" font-family="Segoe UI, Arial, sans-serif">' + t +
            '</text></svg><span class="ctrl-label">Speed ' + t + '</span>';
    }

    // Applies the saved speed. AVPlay offers no way to ask which speeds a TV accepts: if setSpeed
    // throws, the speed goes back to 1x and the TV is told so.
    function applyPlaybackSpeed(announce) {
        var sp = parseFloat(getSetting('speed')) || 1;
        updateSpeedButton();
        if (!state.playerReady || (sp === 1 && !state.speedApplied)) return true;
        try {
            webapis.avplay.setSpeed(sp);
            state.speedApplied = sp !== 1;
            if (announce) showToast(sp === 1 ? 'Normal speed' : 'Speed ' + speedLabel(sp));
            return true;
        } catch (e) {
            console.warn('[AVPlay] setSpeed(' + sp + ') failed:', e && (e.message || e.name || e));
            setSetting('speed', '1');
            try { webapis.avplay.setSpeed(1); } catch (e2) {}
            state.speedApplied = false;
            updateSpeedButton();
            showToast('This TV cannot play at ' + speedLabel(sp) + ' speed');
            return false;
        }
    }

    // ----- Skip intro / outro / recap -----
    // Sources: (1) chapter markers inside local .mkv files, (2) AniSkip (api.aniskip.com), keyed by the
    // MyAnimeList id and episode number. Chapters win when a file has them for the same kind of segment.
    var ANISKIP_URL = 'https://api.aniskip.com/v2/skip-times/';
    var ANISKIP_LENGTH_TOLERANCE = 8;    // s: AniSkip times belong to a cut of this length; a different cut is ignored
    var SKIP_KIND = { 'op': 'intro', 'mixed-op': 'intro', 'ed': 'outro', 'mixed-ed': 'outro', 'recap': 'recap' };
    var SKIP_LABEL = { intro: 'Skip Intro', outro: 'Skip Outro', recap: 'Skip Recap' };
    var skipCache = {};      // 'malId:episode' -> segments
    var malIdCache = {};     // AniList id -> MAL id

    function pickMalId(o) {
        if (!o || typeof o !== 'object') return null;
        var v = parseInt(o.idMal || o.malId, 10);
        return v > 0 ? v : null;
    }
    function findMalId(anime) {
        if (!anime) return null;
        if (malIdCache[anime.mediaId]) return malIdCache[anime.mediaId];
        var raw = anime._raw;
        var id = pickMalId(anime) || pickMalId(raw) || (raw && (pickMalId(raw.media) || pickMalId(raw.anime)));
        if (id) malIdCache[anime.mediaId] = id;
        return id || null;
    }
    // Most library payloads do not carry idMal: ask Seanime for the AniList media details instead.
    function resolveMalId(anime) {
        var id = findMalId(anime);
        if (id) return Promise.resolve(id);
        return api.getMediaDetails(anime.mediaId).then(function (d) {
            var v = pickMalId(d);
            if (v) malIdCache[anime.mediaId] = v;
            return v;
        }).catch(function () { return null; });
    }

    function fetchJsonWithTimeout(url, ms) {
        return new Promise(function (resolve, reject) {
            var timer = setTimeout(function () { reject(new Error('timeout')); }, ms);
            fetch(url).then(function (r) {
                clearTimeout(timer);
                if (!r.ok) { resolve(null); return; }                 // 404 = nothing submitted for this episode
                return r.json().then(resolve);
            }).catch(function (e) { clearTimeout(timer); reject(e); });
        });
    }

    function fetchAniSkip(malId, episode) {
        var key = malId + ':' + episode;
        if (skipCache[key]) return Promise.resolve(skipCache[key]);
        var url = ANISKIP_URL + malId + '/' + episode +
            '?types=op&types=ed&types=mixed-op&types=mixed-ed&types=recap&episodeLength=0';
        return fetchJsonWithTimeout(url, 8000).then(function (data) {
            var out = [];
            var results = (data && data.found && data.results) || [];
            results.forEach(function (r) {
                var kind = r && SKIP_KIND[r.skipType], iv = r && r.interval;
                if (!kind || !iv) return;
                var a = parseFloat(iv.startTime), b = parseFloat(iv.endTime);
                if (!(a >= 0) || !(b > a)) return;
                out.push({ kind: kind, start: a, end: b, length: parseFloat(r.episodeLength) || 0, source: 'aniskip' });
            });
            skipCache[key] = out;
            return out;
        });
    }

    function chapterKind(title) {
        var t = (title || '').trim();
        if (/^(?:opening|intro(?:duction)?|op\d*)(?:\b|$)/i.test(t)) return 'intro';
        if (/^(?:ending|outro|credits|ed\d*)(?:\b|$)/i.test(t)) return 'outro';
        if (/^(?:recap|previously)(?:\b|$)/i.test(t)) return 'recap';
        return null;
    }
    // A chapter lasts until its own end time or, failing that, until the next chapter (null = to the end).
    function chaptersToSegments(chapters) {
        var out = [];
        (chapters || []).forEach(function (c, i) {
            var kind = chapterKind(c.title);
            if (!kind) return;
            var end = c.end > c.start ? c.end : (chapters[i + 1] ? chapters[i + 1].start : null);
            out.push({ kind: kind, start: c.start, end: end, length: 0, source: 'chapters' });
        });
        return out;
    }

    function loadSkipSegments(ctx, token) {
        state.skipData = { aniskip: [], chapters: [] };
        hideSkipPrompt();
        if (getSetting('skipButtons') === 'off') return;
        if (ctx.kind === 'local' && ctx.localPath) {
            loadContainerChapters(ctx.localPath).then(function (chapters) {
                if (token === state.playbackToken) state.skipData.chapters = chaptersToSegments(chapters);
            }).catch(function () {});
        }
        var episode = ctx.episodeNumber;
        if (!(episode >= 1)) return;
        resolveMalId(ctx.anime).then(function (malId) {
            return malId ? fetchAniSkip(malId, episode) : null;
        }).then(function (segments) {
            if (segments && token === state.playbackToken) state.skipData.aniskip = segments;
        }).catch(function (e) { DEBUG && console.log('[Skip] AniSkip unavailable:', e && e.message); });
    }

    function currentSkipSegments(dur) {
        var d = state.skipData;
        if (!d) return [];
        var haveChapters = {};
        d.chapters.forEach(function (s) { haveChapters[s.kind] = true; });
        var out = d.chapters.slice();
        d.aniskip.forEach(function (s) {
            if (haveChapters[s.kind]) return;
            if (s.length > 0 && dur > 0 && Math.abs(s.length - dur) > ANISKIP_LENGTH_TOLERANCE) return;   // timed for another cut
            out.push(s);
        });
        return out;
    }

    function refreshSkipHint() {
        var key = $('#skip-btn-key');
        if (key) key.style.display = controlsShown() ? 'none' : '';      // "OK" chip: OK skips only while the OSD is hidden
    }

    function hideSkipPrompt() {
        state.skipShown = null;
        var btn = $('#skip-btn');
        if (!btn) return;
        btn.classList.add('hidden');
        if (document.activeElement === btn) {
            var pp = $('#ctrl-play-pause');
            if (pp && controlsShown()) { try { pp.focus(); } catch (e) {} } else { try { btn.blur(); } catch (e) {} }
        }
    }

    // Once a second from the progress tick: offer the button while the position is inside a segment.
    function updateSkipPrompt(cur, dur) {
        var btn = $('#skip-btn');
        if (!btn) return;
        if (state.lastSeek && Date.now() - state.lastSeek.at < 2500) cur = state.lastSeek.ms / 1000;
        var seg = null;
        if (!state.playerError && !state.upNext && !state.trackPanelKind && dur > 0) {
            var segs = currentSkipSegments(dur);
            for (var i = 0; i < segs.length; i++) {
                var end = segs[i].end == null ? dur : segs[i].end;
                if (end - segs[i].start >= 5 && cur >= segs[i].start - 0.5 && cur < end - 2) { seg = segs[i]; break; }
            }
        }
        if (!seg) { if (state.skipShown) hideSkipPrompt(); return; }
        if (state.skipShown !== seg) {
            state.skipShown = seg;
            $('#skip-btn-label').textContent = SKIP_LABEL[seg.kind];
            btn.classList.remove('hidden');
        }
        refreshSkipHint();
    }

    function skipNow() {
        var seg = state.skipShown;
        if (!seg || !state.playerReady) return;
        var pos = readPlaybackPosition();
        if (!pos || !(pos.dur > 0)) return;
        var end = seg.end == null ? pos.dur : seg.end;
        hideSkipPrompt();
        // An outro that runs to the end of the file: go straight to the next episode (no 10 s countdown)
        if (seg.kind === 'outro' && pos.dur - end < 5 && hasNextEpisode()) {
            maybeSyncProgress(1, 1);
            playRelativeEpisode(1);
            return;
        }
        seekAbsolute(Math.min(end, pos.dur - 1) * 1000);
        showToast(SKIP_LABEL[seg.kind].replace('Skip ', 'Skipped '), 1500);
    }

    // Returns a promise that resolves once the server has been told to stop.
    // keepStream === true: stop the player only and leave the torrent session running (transcode switch).
    function stopPlayback(keepStream) {
        var pos = state.playerReady ? readPlaybackPosition() : null;
        if (pos) {
            saveContinuity(pos);
            maybeSyncProgress(pos.cur, pos.dur);
        }
        state.playbackToken++;          // invalidates any in-flight start/prepare
        cancelUpNext();
        closeTrackPanel(true);
        cancelScrub(true);
        hideSkipPrompt();
        state.skipData = { aniskip: [], chapters: [] };
        state.torrentInfo = null;
        state.lastSeek = null;
        stopExtSubs();
        stopAppSubs();
        clearSubtitle();
        state.tracks = { audio: [], text: [] };
        state.audioIndex = null;
        state.textIndex = -1;
        if (state.avplayOpen) {
            try { webapis.avplay.stop(); } catch (e) {}
            try { webapis.avplay.close(); } catch (e) {}
        }
        state.avplayOpen = false;
        state.playerReady = false;
        state.isPlaying = false;
        stopProgressTracking();
        var stopPromise = Promise.resolve();
        if (state.activeStreamMediaId && keepStream !== true) {
            stopPromise = api.stopTorrentStream();
            state.activeStreamMediaId = null;
            state.activeStreamEpisode = null;
        }
        state.playbackMediaId = null;
        pendingStreamResolvers = [];
        hideTorrentLoadingOverlay();
        hideBuffering();
        var container = $('#av-player-container');
        if (container) container.innerHTML = '';
        return stopPromise;
    }

    function togglePlayPause() {
        if (state.isPlaying) avplayPause(); else avplayPlay();
    }

    function controlsShown() {
        var c = $('#player-controls');
        return !!c && !c.classList.contains('controls-hidden');
    }
    function showControls() {
        var c = $('#player-controls'); if (!c) return;
        var wasHidden = c.classList.contains('controls-hidden');
        state.controlsVisible = true;
        if (wasHidden) {
            c.classList.remove('controls-hidden');       // only when it really changes: no attribute rewrite per key press
            paintProgress();
            var b = $('#ctrl-play-pause');
            if (b) { try { b.focus(); } catch (e) {} }
        }
        hideControlsAfterDelay();
        refreshSkipHint();
    }
    function hideControls() {
        var c = $('#player-controls'); if (!c) return;
        if (state.scrub) cancelScrub(true);
        if (!c.classList.contains('controls-hidden')) c.classList.add('controls-hidden');
        state.controlsVisible = false;
        if (state.controlsTimer) clearTimeout(state.controlsTimer);
        refreshSkipHint();
    }
    function toggleControls() { if (controlsShown()) hideControls(); else showControls(); }
    function moveCtrlFocus(delta) {
        var btns = document.querySelectorAll('#player-controls .ctrl-btn');
        var idx = -1;
        for (var i = 0; i < btns.length; i++) if (btns[i] === document.activeElement) idx = i;
        if (idx < 0) idx = 2;   // play/pause
        var next = Math.max(0, Math.min(btns.length - 1, idx + delta));
        btns[next].focus();
    }
    function hideControlsAfterDelay() {
        if (state.controlsTimer) clearTimeout(state.controlsTimer);
        state.controlsTimer = setTimeout(function () { if (state.isPlaying && !state.trackPanelKind && !state.scrub) hideControls(); }, 5000);
    }
    function updatePlayPauseButton() {
        var btn = $('#ctrl-play-pause');
        if (!btn) return;
        // keep the floating name label that sits next to the icon
        btn.innerHTML = (state.isPlaying ? ICON_PAUSE : ICON_PLAY) +
            '<span class="ctrl-label">' + (state.isPlaying ? 'Pause' : 'Play') + '</span>';
        btn.setAttribute('aria-label', state.isPlaying ? 'Pause' : 'Play');
    }

    var progressInterval = null;
    // The OSD's time labels and bar are only touched while the OSD is visible, and only when
    // their text/width actually changed: needless repaints over the video make the OSD flicker.
    function paintProgress() {
        var p = state.osdProgress;
        if (!p) return;
        var fill = $('#progress-fill'), cur = $('#current-time'), tot = $('#total-time');
        if (fill && fill._v !== p.pct) { fill._v = p.pct; fill.style.width = p.pct; }
        if (cur && cur._v !== p.cur) { cur._v = p.cur; cur.textContent = p.cur; }
        if (tot && tot._v !== p.total) { tot._v = p.total; tot.textContent = p.total; }
    }
    function updateProgressUI(cur, dur) {
        state.osdProgress = {
            pct: (Math.round((cur / dur) * 1000) / 10) + '%',
            cur: formatTime(cur),
            total: formatTime(dur)
        };
        if (controlsShown()) paintProgress();         // otherwise it is painted when the OSD appears
    }

    function startProgressTracking() {
        stopProgressTracking();
        progressInterval = setInterval(function () {
            if (!state.playerReady) return;
            if (state.buffering && Date.now() - state.bufferingSince > 60000) {
                failPlayback({ title: 'The stream stalled', message: 'It has been buffering for over a minute. The torrent may be slow, or the connection is weak.', canRetry: true });
                return;
            }
            try {
                var currentTime = webapis.avplay.getCurrentTime() / 1000;
                var duration = webapis.avplay.getDuration() / 1000;
                if (duration > 0) {
                    updateProgressUI(currentTime, duration);
                    maybeSyncProgress(currentTime, duration);
                    updateSkipPrompt(currentTime, duration);
                    if (state.isPlaying && Date.now() - state.lastContinuitySave > CONTINUITY_INTERVAL) {
                        saveContinuity({ cur: currentTime, dur: duration });
                    }
                }
            } catch (e) {}
        }, 1000);
    }
    function stopProgressTracking() {
        if (progressInterval) { clearInterval(progressInterval); progressInterval = null; }
    }

    function formatTime(seconds) {
        var h = Math.floor(seconds / 3600);
        var m = Math.floor((seconds % 3600) / 60);
        var s = Math.floor(seconds % 60);
        function pad(n) { return n < 10 ? '0' + n : '' + n; }
        if (h > 0) return h + ':' + pad(m) + ':' + pad(s);
        return pad(m) + ':' + pad(s);
    }

    // ===== Tizen IME =====
    function setupTizenIME(element) {
        if (typeof webapis === 'undefined' || !webapis.ime) return;
        try { webapis.ime.setKeyboardInput(element); } catch (e) {}
    }
    function showIME() {
        if (typeof webapis === 'undefined' || !webapis.ime) return;
        try { webapis.ime.show(); } catch (e) {}
    }
    function hideIME() {
        if (typeof webapis === 'undefined' || !webapis.ime) return;
        try { webapis.ime.hide(); } catch (e) {}
    }

    // ===== Setup Screen =====
    function openSetupScreen() {
        showScreen('setup');
        var urlInput = $('#server-url-input');
        var pwInput = $('#server-password-input');
        var connectBtn = $('#connect-btn');
        urlInput.value = localStorage.getItem(STORAGE_KEYS.SERVER_URL) || '';
        pwInput.value = '';   // the password is never saved, only its hash
        $('#setup-error').textContent = '';
        connectBtn.textContent = 'Connect';
        setupTizenIME(urlInput);
        setupTizenIME(pwInput);
        setTimeout(function () {
            try {
                urlInput.focus();
                urlInput.setSelectionRange(urlInput.value.length, urlInput.value.length);
                showIME();
            } catch (e) {}
        }, 300);
    }

    // ===== Library Loading =====
    function loadLibrary() {
        return api.getLibraryCollection().then(function (coll) {
            state.library = coll.entries;
            var cw = coll.continueWatching;
            if (!cw || cw.length === 0) {
                return api.getHomeItems().then(function (homeItems) {
                    if (homeItems && homeItems.length > 0) return homeItems;
                    DEBUG && console.log('[Session] Deriving continue-watching from library entries');
                    return deriveContinueWatching(coll.entries);
                });
            }
            return cw;
        }).then(function (cw) {
            state.continueWatching = cw || [];
            DEBUG && console.log('[Session] continue-watching items:', state.continueWatching.length);
            renderLibrary(state.library);
            renderHeroCarousel(state.continueWatching);
            loadStatusSections();
        }).catch(function (e) {
            console.error('[Session] Failed to load library:', e);
        });
    }

    // ===== Views: Home / Discover =====
    function setView(view) {
        state.view = view;
        $('#content-area').style.display = view === 'home' ? '' : 'none';
        $('#discover-area').style.display = view === 'discover' ? '' : 'none';
        $('#schedule-area').style.display = view === 'schedule' ? '' : 'none';
        $('#queue-area').style.display = view === 'queue' ? '' : 'none';
        $('#profile-area').style.display = view === 'profile' ? '' : 'none';
        $('#nav-home').className = 'nav-btn' + (view === 'home' ? ' active' : '');
        $('#nav-discover').className = 'nav-btn' + (view === 'discover' ? ' active' : '');
        $('#nav-schedule').className = 'nav-btn' + (view === 'schedule' ? ' active' : '');
        $('#nav-queue').className = 'nav-btn' + (view === 'queue' ? ' active' : '');
        $('#nav-profile').className = 'nav-btn' + (view === 'profile' ? ' active' : '');
        if (view === 'discover') loadDiscover(false);
        if (view === 'schedule') loadSchedule(false);
        if (view === 'queue') loadQueue();
        if (view === 'profile') loadProfile();
        imgSchedule(60);
    }

    // ===== Airing schedule (anime on the user's lists) =====
    var SCHEDULE_CACHE_MS = 10 * 60 * 1000;
    var WEEKDAYS = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'];
    var scheduleSeq = 0;

    function pad2(n) { return (n < 10 ? '0' : '') + n; }
    function startOfDay(d) { return new Date(d.getFullYear(), d.getMonth(), d.getDate()); }
    function dayKey(d) { return d.getFullYear() + '-' + pad2(d.getMonth() + 1) + '-' + pad2(d.getDate()); }
    function dayLabel(d, today) {
        var diff = Math.round((startOfDay(d).getTime() - startOfDay(today).getTime()) / 86400000);
        if (diff === 0) return 'Today';
        if (diff === 1) return 'Tomorrow';
        if (diff === -1) return 'Yesterday';
        return WEEKDAYS[d.getDay()];
    }

    // Yesterday through the next 6 days, grouped per local day. Titles hidden by the
    // adult/ecchi filter (known from the user's lists) never appear here.
    function groupSchedule(items, now) {
        var today = startOfDay(now).getTime();
        var from = today - 86400000, to = today + 7 * 86400000;
        var map = {}, days = [];
        (items || []).forEach(function (it) {
            if (!it || !it.dateTime || state.blockedIds[it.mediaId]) return;
            var d = new Date(it.dateTime), t = d.getTime();
            if (isNaN(t) || t < from || t >= to) return;
            var k = dayKey(d);
            if (!map[k]) { map[k] = { date: startOfDay(d), items: [] }; days.push(map[k]); }
            map[k].items.push({ item: it, date: d });
        });
        days.sort(function (a, b) { return a.date.getTime() - b.date.getTime(); });
        days.forEach(function (day) {
            day.items.sort(function (a, b) { return a.date.getTime() - b.date.getTime(); });
        });
        return days;
    }

    function scheduleCard(entry, nowMs) {
        var it = entry.item, d = entry.date;
        var aired = d.getTime() < nowMs;
        var card = document.createElement('div');
        card.className = 'anime-card schedule-card' + (aired ? ' aired' : '');
        card.tabIndex = 0;
        var img = document.createElement('img');
        img.alt = it.title;
        lazyImage(img, it.image);
        var info = document.createElement('div');
        info.className = 'card-info';
        var title = document.createElement('div');
        title.className = 'card-title';
        title.textContent = it.title;
        var meta = document.createElement('div');
        meta.className = 'card-meta';
        meta.textContent = pad2(d.getHours()) + ':' + pad2(d.getMinutes()) + '  \u00B7  ' +
            (it.isMovie ? 'Movie' : 'Ep ' + it.episodeNumber) + (it.isSeasonFinale ? '  \u00B7  Finale' : '');
        info.appendChild(title); info.appendChild(meta);
        card.appendChild(img); card.appendChild(info);
        var open = function () {
            state.lastCard = card;
            openAnimeDetail(normalizeAnime({
                id: it.mediaId, title: { userPreferred: it.title }, coverImage: { large: it.image, extraLarge: it.image }
            }));
        };
        card.addEventListener('click', open);
        card.addEventListener('keydown', function (e) {
            if (e.keyCode === KEY_CODES.ENTER) { e.preventDefault(); open(); }
        });
        return card;
    }

    function renderSchedule(items) {
        var host = $('#schedule-rows');
        host.innerHTML = '';
        var now = new Date();
        var days = groupSchedule(items, now);
        if (days.length === 0) {
            host.innerHTML = '<p class="empty-note">Nothing airs from your lists this week. Add airing shows to Watching or Planning on AniList.</p>';
            return;
        }
        days.forEach(function (day) {
            var section = document.createElement('section');
            section.className = 'content-section';
            var title = document.createElement('h2');
            title.className = 'section-title';
            title.textContent = dayLabel(day.date, now);
            var sub = document.createElement('span');
            sub.className = 'section-count';
            sub.textContent = WEEKDAYS[day.date.getDay()] + ', ' + MONTHS[day.date.getMonth()] + ' ' + day.date.getDate();
            title.appendChild(sub);
            var row = document.createElement('div');
            row.className = 'card-row';
            section.appendChild(title);
            section.appendChild(row);
            host.appendChild(section);
            day.items.forEach(function (entry) { row.appendChild(scheduleCard(entry, now.getTime())); });
        });
        // start on the first episode that has not aired yet
        var upcoming = host.querySelector('.schedule-card:not(.aired)');
        if (upcoming && upcoming.scrollIntoView) { /* focus handling stays with the remote */ }
    }

    // P0 – Queue + Profile helpers (server has no /queue or /viewer route)
    function renderQueue(items) {
        var note = $('#queue-note');
        var host = $('#queue-rows');
        if (!host) return;
        host.innerHTML = '';
        if (note) note.style.display = 'none';
        if (!items || !items.length) {
            if (note) { note.textContent = 'No queue on this server. Manage torrents from Seanime web/desktop.'; note.style.display = ''; }
            else host.innerHTML = '<p class="empty-note">No queue on this server.</p>';
            return;
        }
        items.forEach(function (it) {
            var row = document.createElement('div');
            row.className = 'queue-item'; row.tabIndex = 0;
            var title = document.createElement('span'); title.textContent = it.name || it.torrentName || 'Torrent';
            var meta = document.createElement('span'); meta.textContent = (it.progress != null ? Math.round(it.progress) + '%' : '') + (it.state ? '  \u00B7  ' + it.state : '');
            row.appendChild(title); row.appendChild(meta);
            host.appendChild(row);
        });
    }
    function loadQueue() {
        renderQueue([]);
    }
    // Header, totals, per-list counts, distribution bar and health line.
    // Safe to call again when the AniList collection finishes loading.
    function profileRenderSummary() {
        profileRenderHeader();
        var stats = $('#profile-stats');
        if (stats) {
            stats.innerHTML = '';
            var tw = profileTimeWatched();
            var row = document.createElement('div'); row.className = 'profile-stats';
            var hrs = Math.floor(tw.minutes / 60);
            [[String(profileTotalTitles()),'Titles'], [String(tw.episodes),'Episodes'], [hrs + 'h','Watched']].forEach(function (p) {
                var box = document.createElement('div');
                box.innerHTML = '<div class="profile-stat-val">' + escapeHtml(p[0]) + '</div><div class="profile-stat-label">' + escapeHtml(p[1]) + '</div>';
                row.appendChild(box);
            });
            stats.appendChild(row);
        }
        profileRenderListStats();
        profileRenderDistribution();
    }
    function loadProfile() {
        var note = $('#profile-note');
        if (note) note.style.display = 'none';
        profileRenderSummary();
        profileRenderActivity();
        // the per-list counts come from the AniList collection: fetch it if Home has not yet
        if (!state.profileStats && !state.profileStatsLoading) {
            state.profileStatsLoading = true;
            loadStatusSections().then(function () { state.profileStatsLoading = false; });
        }
    }

    function loadSchedule(force) {
        if (!force && state.scheduleLoadedAt && Date.now() - state.scheduleLoadedAt < SCHEDULE_CACHE_MS) return;
        var seq = ++scheduleSeq;
        var host = $('#schedule-rows');
        host.innerHTML = '<p class="empty-note">Loading schedule\u2026</p>';
        var ready = state.listProgressLoaded ? Promise.resolve() : loadStatusSections();
        Promise.all([api.getSchedule(), ready]).then(function (r) {
            if (seq !== scheduleSeq) return;
            // without the user's lists the adult/ecchi filter cannot be applied: show nothing
            if (!state.listProgressLoaded) throw new Error('lists not available');
            state.scheduleLoadedAt = Date.now();
            renderSchedule(r[0]);
        }).catch(function (e) {
            if (seq !== scheduleSeq) return;
            console.warn('[Schedule] failed:', e && e.message);
            state.scheduleLoadedAt = 0;
            host.innerHTML = '<p class="empty-note">Could not load the schedule.</p>';
        });
    }

    // ===== Discover =====
    var DISCOVER_CACHE_MS = 10 * 60 * 1000;   // reuse loaded rows for 10 minutes

    function currentSeasonInfo() {
        var d = new Date(), m = d.getMonth();
        return {
            season: m <= 2 ? 'WINTER' : (m <= 5 ? 'SPRING' : (m <= 8 ? 'SUMMER' : 'FALL')),
            year: d.getFullYear()
        };
    }

    var DISCOVER_ROWS = [
        { title: 'Trending Now', params: function () { return { sort: ['TRENDING_DESC'] }; } },
        { title: 'Airing Now', params: function () { return { status: ['RELEASING'], sort: ['POPULARITY_DESC'] }; } },
        { title: 'Popular This Season', params: function () {
            var si = currentSeasonInfo();
            return { season: si.season, seasonYear: si.year, sort: ['POPULARITY_DESC'] };
        } },
        { title: 'Top Rated', params: function () { return { sort: ['SCORE_DESC'], averageScore_greater: 75 }; } },
        { title: 'All-Time Popular', params: function () { return { sort: ['POPULARITY_DESC'] }; } }
    ];

    function resetDiscover() {
        state.discoverLoadedAt = 0;
        state.discoverSeq++;
        var host = $('#discover-rows');
        if (host) host.innerHTML = '';
    }

    // P0.2 - Discover: full AniList explorer (all filters combinable via Seanime listAnime)
    // Ecchi is NOT listed – adult titles are permanently hidden on this TV build.
    var DISC_GENRES = ['Action','Adventure','Comedy','Drama','Fantasy','Sci-Fi','Romance','Slice of Life','Sports','Mystery','Horror','Supernatural','Mecha','Music','Thriller','Psychological'];
    var DISC_FORMATS = [{ v: '', l: 'All formats' },{ v: 'TV', l: 'TV' },{ v: 'MOVIE', l: 'Movie' },{ v: 'OVA', l: 'OVA' },{ v: 'SPECIAL', l: 'Special' },{ v: 'TV_SHORT', l: 'TV Short' }];
    var DISC_STATUS = [{ v: '', l: 'All status' },{ v: 'RELEASING', l: 'Airing' },{ v: 'FINISHED', l: 'Finished' },{ v: 'NOT_YET_RELEASED', l: 'Upcoming' },{ v: 'HIATUS', l: 'Hiatus' },{ v: 'CANCELLED', l: 'Cancelled' }];
    var DISC_SORTS = [{ v: 'POPULARITY_DESC', l: 'Popular' },{ v: 'TRENDING_DESC', l: 'Trending' },{ v: 'SCORE_DESC', l: 'Top rated' },{ v: 'START_DATE_DESC', l: 'Newest' },{ v: 'FAVOURITES_DESC', l: 'Most favourited' }];
    function renderDiscoverFilters() {
        var host = $('#discover-filters');
        if (!host) return;
        host.innerHTML = '';
        function group(label, opts, key) {
            opts.forEach(function (o) {
                var v = (typeof o === 'string') ? o : o.v;
                var l = (typeof o === 'string') ? o : o.l;
                var b = document.createElement('button');
                b.className = 'df-chip' + (String(state.discFilters[key] || '') === String(v) ? ' active' : '');
                b.tabIndex = 0; b.textContent = l;
                b.addEventListener('click', function () { state.discFilters[key] = v; state.discPage = 1; renderDiscoverFilters(); loadDiscover(true); });
                b.addEventListener('keydown', function (e) { if (e.keyCode === KEY_CODES.ENTER) { e.preventDefault(); b.click(); } });
                host.appendChild(b);
            });
        }
        group('genre', DISC_GENRES, 'genre');
        group('format', DISC_FORMATS, 'format');
        group('status', DISC_STATUS, 'status');
        group('sort', DISC_SORTS, 'sort');
        var y = new Date().getFullYear();
        var years = [{ v: '', l: 'Any year' }];
        for (var yy = y; yy >= 1995; yy--) years.push({ v: String(yy), l: String(yy) });
        years.slice(0, 10).forEach(function (o) {
            var b = document.createElement('button');
            b.className = 'df-chip' + (String(state.discFilters.year || '') === String(o.v) ? ' active' : '');
            b.tabIndex = 0; b.textContent = o.l;
            b.addEventListener('click', function () { state.discFilters.year = o.v; state.discPage = 1; renderDiscoverFilters(); loadDiscover(true); });
            host.appendChild(b);
        });
        // Reset row – last so keyboard nav can wrap to it quickly
        var reset = document.createElement('button');
        reset.className = 'df-chip'; reset.tabIndex = 0; reset.textContent = 'Reset filters';
        reset.addEventListener('click', function () { state.discFilters = { genre: '', format: '', status: '', sort: 'POPULARITY_DESC', year: '' }; state.discPage = 1; renderDiscoverFilters(); loadDiscover(true); });
        reset.addEventListener('keydown', function (e) { if (e.keyCode === KEY_CODES.ENTER) { e.preventDefault(); reset.click(); } });
        host.appendChild(reset);
    }
    function discoverParamsForRow(def) {
        var f = state.discFilters;
        var p = {};
        // global filters are combinable: genre+format+status+year+sort all at once
        if (f.genre) p.genre = f.genre;
        if (f.format) p.format = [f.format];
        if (f.status) p.status = [f.status];
        if (f.year) p.seasonYear = parseInt(f.year, 10);
        var base = def.params();
        for (var k in base) p[k] = base[k];
        // row intrinsic sort wins; global sort only when row has no sort
        if (f.sort && !base.sort) p.sort = [f.sort];
        else if (f.sort && base.sort && f.sort !== base.sort[0]) {
            // if global sort is explicitly chosen by user, override row sort (e.g. user taps "Score")
            p.sort = [f.sort];
        }
        // adult permanently hidden: listAnime POST isAdult:false always
        return p;
    }
    // Bug 8 mitigation: cache is bypassed when filters/page changed; paging label per page param
    var _prevDiscoverKey = '';
    function discoverCacheKey() {
        var f = state.discFilters;
        return [f.genre || '', f.format || '', f.status || '', f.sort || '', f.year || '', state.discPage].join('|');
    }
    function renderDiscoverPaging() {
        var host = $('#discover-paging');
        if (!host) return;
        host.innerHTML = '';
        var prev = document.createElement('button');
        prev.className = 'pg-btn'; prev.tabIndex = 0; prev.textContent = 'Prev'; prev.disabled = state.discPage <= 1;
        prev.addEventListener('click', function () { if (state.discPage > 1) { state.discPage--; loadDiscover(true); } });
        prev.addEventListener('keydown', function (e) { if (e.keyCode === KEY_CODES.ENTER) { e.preventDefault(); prev.click(); } });
        var label = document.createElement('span');
        label.className = 'pg-label'; label.textContent = 'Page ' + state.discPage + ' \u00B7 all rows';
        var next = document.createElement('button');
        next.className = 'pg-btn'; next.tabIndex = 0; next.textContent = 'Next';
        next.addEventListener('click', function () { state.discPage++; loadDiscover(true); });
        next.addEventListener('keydown', function (e) { if (e.keyCode === KEY_CODES.ENTER) { e.preventDefault(); next.click(); } });
        host.appendChild(prev); host.appendChild(label); host.appendChild(next);
        // D-pad: focus first paging button when no discover card focused
        var anyCard = document.querySelector('#discover-rows .anime-card');
        if (!anyCard && prev && !prev.disabled) {
            // leave focus on paging controls after a page change
        }
    }
    function loadDiscover(force) {
        var key = discoverCacheKey();
        if (!force && state.discoverLoadedAt && Date.now() - state.discoverLoadedAt < DISCOVER_CACHE_MS && key === _prevDiscoverKey) return;
        var seq = ++state.discoverSeq;
        state.discoverLoadedAt = Date.now();
        _prevDiscoverKey = key;
        renderDiscoverFilters();
        var host = $('#discover-rows');
        host.innerHTML = '';
        DISCOVER_ROWS.forEach(function (def) {
            var section = document.createElement('section');
            section.className = 'content-section';
            var title = document.createElement('h2');
            title.className = 'section-title';
            title.textContent = def.title;
            var row = document.createElement('div');
            row.className = 'card-row';
            row.innerHTML = '<p class="empty-note">Loading\u2026</p>';
            section.appendChild(title);
            section.appendChild(row);
            host.appendChild(section);
            var params = discoverParamsForRow(def);
            params.page = state.discPage;
            params.perPage = 24;
            api.listAnime(params).then(function (media) {
                if (seq !== state.discoverSeq) return;
                var items = media.map(normalizeAnime).filter(function (x) { return x && x.mediaId; });
                row.innerHTML = '';
                if (items.length === 0) { section.style.display = 'none'; return; }
                appendCardBatch(row, items, 0);
            }).catch(function (e) {
                if (seq !== state.discoverSeq) return;
                console.warn('[Discover] ' + def.title + ' failed:', e);
                state.discoverLoadedAt = 0;
                row.innerHTML = '<p class="empty-note">Could not load this list.</p>';
            });
        });
        renderDiscoverPaging();
    }

    // ===== Settings =====
    var LANG_ORDER = ['jpn', 'eng', 'spa', 'fre', 'ger', 'ita', 'por', 'rus', 'chi', 'kor', 'ara', 'hin', 'tha', 'ind', 'vie', 'pol', 'tur'];
    var LANG_OPTIONS = LANG_ORDER.map(function (k) { return { v: k, l: LANG_NAMES[k] }; });
    var ON_OFF = [{ v: 'on', l: 'On' }, { v: 'off', l: 'Off' }];

    var SETTING_DEFS = [
        { section: 'Playback' },
        { key: 'autoNext', label: 'Auto-play next episode', sub: 'Counts down 10 seconds after an episode ends', options: ON_OFF, def: 'on' },
        { key: 'preferLocal', label: 'Play from disk when available', sub: 'Uses files in your Seanime library instead of streaming a torrent', options: ON_OFF, def: 'on' },
        { key: 'resume', label: 'Resume where you left off', sub: 'Needs watch continuity enabled on the server', options: ON_OFF, def: 'on' },
        { key: 'transcode', label: 'Transcode unsupported video', sub: 'If the TV cannot decode a release (AV1, 10-bit HEVC), the server converts it. Needs ffmpeg on the server', options: ON_OFF, def: 'on' },
        { key: 'watchedAt', label: 'Mark as watched at', sub: 'Updates your AniList progress', def: '0.8',
          options: [{ v: '0.7', l: '70%' }, { v: '0.8', l: '80%' }, { v: '0.9', l: '90%' }] },
        { key: 'speed', label: 'Playback speed', sub: 'Remembered between episodes. Not every TV supports every speed', options: SPEED_OPTIONS, def: '1' },
        { key: 'skipButtons', label: 'Skip intro / outro buttons', sub: 'Looks up skip times on AniSkip (sends the MyAnimeList id and episode number)', options: ON_OFF, def: 'on' },

        { section: 'Language' },
        { key: 'audio', pref: true, label: 'Preferred audio', def: 'jpn', options: LANG_OPTIONS },
        { key: 'sub', pref: true, label: 'Preferred subtitles', def: 'eng',
          options: [{ v: 'off', l: 'Off' }].concat(LANG_OPTIONS) },
        { key: 'titleLang', label: 'Title language', def: 'default',
          options: [{ v: 'default', l: 'AniList default' }, { v: 'romaji', l: 'Romaji' },
                    { v: 'english', l: 'English' }, { v: 'native', l: 'Native' }] },

        { section: 'Subtitles' },
        { key: 'subMode', label: 'Subtitle rendering', sub: 'Auto switches to TV if no subtitle text reaches the app', def: 'app',
          options: [{ v: 'auto', l: 'Auto' }, { v: 'app', l: 'App (styled)' }, { v: 'tv', l: 'TV (native)' }] },
        { key: 'subSize', label: 'Subtitle size', def: '46',
          options: [{ v: '34', l: 'Small' }, { v: '46', l: 'Medium' }, { v: '58', l: 'Large' }, { v: '72', l: 'Extra large' }] },
        { key: 'subPos', label: 'Subtitle position', def: '150',
          options: [{ v: '90', l: 'Low' }, { v: '150', l: 'Default' }, { v: '250', l: 'High' }] },
        // P1: online subtitle search + provider toggle
        { section: 'Subtitles Online' },
        { key: 'onlineSubs', label: 'Online subtitle search', sub: 'Search OpenSubtitles / Jimaku when no sidecar exists (via Seanime extension)', options: ON_OFF, def: 'off' },

        // Content: adult gate removed – ecchi/adult never shown on TV

        { section: 'Server' },
        { info: true, label: 'Server', value: function () { return CONFIG.serverUrl || '\u2014'; } },
        { info: true, label: 'Connection', value: function () {
            var d = $('#connection-status');
            return d && d.className.indexOf('online') >= 0 ? 'Online' : 'Offline';
        } },
        { info: true, label: 'App version', value: function () { return '1.0.0'; } },
        { key: 'staySignedIn', label: 'Stay signed in', sub: 'Off forgets the saved login when the app closes', options: ON_OFF, def: 'on' },
        { action: 'test', label: 'Test connection' },
        { action: 'reset', label: 'Reset settings to defaults' },
        { action: 'logout', label: 'Log out / change server', danger: true }
    ];

    var SETTING_BY_KEY = {};
    SETTING_DEFS.forEach(function (d) { if (d.key) SETTING_BY_KEY[d.key] = d; });

    function settingStorageKey(d) { return d.pref ? d.key : 'set_' + d.key; }
    function getSetting(key) {
        var d = SETTING_BY_KEY[key];
        if (!d) return null;
        return getPref(settingStorageKey(d), d.def);
    }
    function setSetting(key, value) {
        var d = SETTING_BY_KEY[key];
        if (d) setPref(settingStorageKey(d), value);
    }

    var CHEV_L = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><polyline points="15 18 9 12 15 6"/></svg>';
    var CHEV_R = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><polyline points="9 18 15 12 9 6"/></svg>';

    // options plus the current value (the track picker can store languages not in the list)
    function settingOptions(def, cur) {
        var opts = def.options.slice();
        for (var i = 0; i < opts.length; i++) if (opts[i].v === cur) return opts;
        opts.push({ v: cur, l: def.pref ? langName(cur) : String(cur) });
        return opts;
    }
    function settingLabelFor(def, cur) {
        var opts = settingOptions(def, cur);
        for (var i = 0; i < opts.length; i++) if (opts[i].v === cur) return opts[i].l;
        return String(cur);
    }

    function renderSettings() {
        var list = $('#settings-list');
        list.innerHTML = '';
        SETTING_DEFS.forEach(function (def) {
            if (def.section) {
                var h = document.createElement('div');
                h.className = 'settings-section';
                h.textContent = def.section;
                list.appendChild(h);
                return;
            }
            var row = document.createElement('div');
            row.className = 'setting-row';
            var label = document.createElement('span');
            label.className = 'setting-label';
            label.textContent = def.label;
            if (def.sub) {
                var sub = document.createElement('span');
                sub.className = 'setting-sub';
                sub.textContent = def.sub;
                label.appendChild(sub);
            }
            var value = document.createElement('span');
            value.className = 'setting-value';
            var val = document.createElement('span');
            val.className = 'set-val';

            if (def.info) {
                row.className += ' setting-info';
                val.textContent = def.value();
                value.appendChild(val);
            } else if (def.action) {
                row.className += ' setting-focusable setting-action' + (def.danger ? ' danger' : '');
                row.tabIndex = 0;
                row._action = def.action;
            } else {
                row.className += ' setting-focusable';
                row.tabIndex = 0;
                row._def = def;
                var l = document.createElement('span'); l.className = 'set-arrow'; l.innerHTML = CHEV_L;
                var r = document.createElement('span'); r.className = 'set-arrow'; r.innerHTML = CHEV_R;
                val.textContent = settingLabelFor(def, getSetting(def.key));
                value.appendChild(l); value.appendChild(val); value.appendChild(r);
            }
            row.appendChild(label);
            row.appendChild(value);
            row.addEventListener('click', function () { activateSettingRow(row); });
            list.appendChild(row);
        });
    }

    function cycleSetting(row, delta) {
        var def = row._def;
        if (!def) return;
        var cur = getSetting(def.key);
        var opts = settingOptions(def, cur);
        var idx = 0;
        for (var i = 0; i < opts.length; i++) if (opts[i].v === cur) idx = i;
        var next = opts[(idx + delta + opts.length) % opts.length];
        setSetting(def.key, next.v);
        row.querySelector('.set-val').textContent = next.l;
        if (def.key === 'titleLang') state.settingsDirty = true;
        if (def.key === 'staySignedIn') persistCredentials();
        if (def.key === 'subSize' || def.key === 'subPos') applySubtitleStyle();
    }

    function actionValueEl(row) {
        var v = row.querySelector('.set-val');
        if (!v) { v = document.createElement('span'); v.className = 'set-val'; row.querySelector('.setting-value').appendChild(v); }
        return v;
    }

    // Checks the server, the login and the live-events socket, and says which one fails.
    function runConnectionTest(row) {
        var parts = [/^https:/i.test(CONFIG.serverUrl) ? 'HTTPS' : 'HTTP'];
        var set = function (t) { actionValueEl(row).textContent = t; };
        set('Testing\u2026');
        api.request('/status').then(function (data) {
            var d = unwrapData(data);
            parts.push('Server OK');
            parts.push(CONFIG.passwordHash && d && d.user === null ? 'Not signed in' : 'Signed in');
            set(parts.join('  \u2022  ') + '  \u2022  Events\u2026');
            return connectWebSocket().then(function () { parts.push('Events OK'); },
                                           function () { parts.push('Events FAILED'); });
        }, function () {
            parts.push('Server FAILED');
            if (parts[0] === 'HTTPS') parts.push('certificate not trusted?');
        }).then(function () { set(parts.join('  \u2022  ')); });
    }

    var resetArmedUntil = 0;
    function activateSettingRow(row) {
        if (row._def) { cycleSetting(row, 1); return; }
        if (row._action === 'logout') { logout(); return; }
        if (row._action === 'test') { runConnectionTest(row); return; }
        if (row._action === 'reset') {
            var valEl = actionValueEl(row);
            if (Date.now() < resetArmedUntil) {
                SETTING_DEFS.forEach(function (d) {
                    if (d.key) { delete prefCache[settingStorageKey(d)]; try { localStorage.removeItem('seanime_pref_' + settingStorageKey(d)); } catch (e) {} }
                });
                resetArmedUntil = 0;
                state.settingsDirty = true;
                applySubtitleStyle();
                renderSettings();
                var again = document.querySelector('#settings-list .setting-action');
                if (again) { again.focus(); again.querySelector('.setting-value').innerHTML = '<span class="set-val">Done</span>'; }
            } else {
                resetArmedUntil = Date.now() + 4000;
                valEl.textContent = 'Press OK again to confirm';
                setTimeout(function () { if (Date.now() >= resetArmedUntil && valEl.parentNode) valEl.textContent = ''; }, 4100);
            }
        }
    }

    function openSettings() {
        state.settingsDirty = false;
        resetArmedUntil = 0;
        renderSettings();
        showScreen('settings');
        var first = document.querySelector('#settings-list .setting-focusable');
        if (first) first.focus();
    }

    function closeSettings() {
        showScreen('home');
        if (state.settingsDirty) {
            // titles changed language: reload everything that shows titles
            state.settingsDirty = false;
            clearSearchResults();
            resetDiscover();
            if (state.view === 'discover') loadDiscover(true);
            loadLibrary();
        }
        var b = $('#settings-btn');
        if (b) { try { b.focus(); } catch (e) {} }
    }

    function moveSettingsFocus(delta) {
        var rows = document.querySelectorAll('#settings-list .setting-focusable');
        var idx = -1;
        for (var i = 0; i < rows.length; i++) if (rows[i] === document.activeElement) idx = i;
        var next = Math.max(0, Math.min(rows.length - 1, idx < 0 ? 0 : idx + delta));
        if (rows[next]) rows[next].focus();
    }

    function handleSettingsKeys(keyCode, e) {
        var K = KEY_CODES;
        var row = document.activeElement;
        var isRow = row && row.classList && row.classList.contains('setting-focusable');
        if (keyCode === K.UP) { e.preventDefault(); moveSettingsFocus(-1); }
        else if (keyCode === K.DOWN) { e.preventDefault(); moveSettingsFocus(1); }
        else if (keyCode === K.LEFT && isRow && row._def) { e.preventDefault(); cycleSetting(row, -1); }
        else if (keyCode === K.RIGHT && isRow && row._def) { e.preventDefault(); cycleSetting(row, 1); }
        else if (keyCode === K.ENTER && isRow) { e.preventDefault(); activateSettingRow(row); }
        else if (keyCode === K.RETURN) { closeSettings(); }
    }

    // ===== Manual torrent choice =====
    // Searches the server's torrent providers for an episode and lets the user pick the
    // exact release (and, for batch torrents, the file) instead of automatic selection.
    function baseMediaFor(anime) {
        var r = anime._raw || {};
        var m = r.media || r.baseAnime || r.anime || (r.id ? r : null);
        if (m && m.id) return m;
        return { id: anime.mediaId, title: { userPreferred: anime.title, english: anime.title },
                 episodes: anime.episodes || null, format: anime.format || null, status: anime.status || null,
                 genres: anime.genres || [], synonyms: [] };
    }

    function pickerSearchBody(p, type, query) {
        return { type: type, provider: '', query: query || '', episodeNumber: p.episodeNumber, batch: type === 'smart' ? p.batch : false,
                 media: baseMediaFor(p.anime), absoluteOffset: 0, resolution: '', bestRelease: false, includeSpecialProviders: false };
    }

    function openTorrentPicker(anime, episodeNumber, aniDb, fromError) {
        state.picker = {
            anime: anime, episodeNumber: episodeNumber, aniDb: aniDb || null, batch: false, step: 'results',
            torrents: [], files: [], torrent: null, loading: true, error: '', seq: 0,
            fromError: !!fromError, returnFocus: document.activeElement
        };
        $('#torrent-picker').classList.remove('hidden');
        runTorrentSearch();
    }

    function closeTorrentPicker() {
        var p = state.picker;
        state.picker = null;
        $('#torrent-picker').classList.add('hidden');
        if (!p) return;
        if (p.fromError && state.playerErrorInfo && state.currentScreen === 'player' && !state.avplayOpen) {
            renderPlayerError(state.playerErrorInfo);
        } else if (state.currentScreen === 'player' && !state.avplayOpen && !state.playerError) {
            // opened from next/previous episode while the player screen was showing: nothing is
            // playing and nothing was chosen, so go back instead of leaving a black screen
            leavePlayer();
        } else if (p.returnFocus && document.body.contains(p.returnFocus)) {
            try { p.returnFocus.focus(); } catch (e) {}
        }
    }

    function runTorrentSearch() {
        var p = state.picker;
        if (!p) return;
        var seq = ++p.seq;
        p.loading = true; p.error = ''; p.step = 'results';
        renderPicker();
        api.searchTorrents(pickerSearchBody(p, 'smart')).then(function (data) {
            var list = (data && data.torrents) || [];
            if (list.length || p.batch) return list;
            // second fallback: always try absolute numbering with AniDB context if available
            var fallbackAniDb = p.aniDb || null;
            if (!fallbackAniDb) {
                var eps = detailEpisodes();
                for (var i = 0; i < eps.length; i++) {
                    var en = eps[i].episodeNumber || eps[i].number;
                    if (en === p.episodeNumber && eps[i].aniDBEpisode) { fallbackAniDb = eps[i].aniDBEpisode; break; }
                }
            }
            if (fallbackAniDb) {
                var smartBody2 = pickerSearchBody(p, 'smart');
                // retry smart with resolved aniDb (covers detail-Play before episode bundle loaded)
                p.aniDb = fallbackAniDb;
                var body2 = pickerSearchBody(p, 'smart');
                return api.searchTorrents(body2).then(function (d2) {
                    var l2 = (d2 && d2.torrents) || [];
                    if (l2.length) return l2;
                    return api.searchTorrents(pickerSearchBody(p, 'simple', p.anime.title + ' ' + pad2(p.episodeNumber)))
                        .then(function (d3) { return (d3 && d3.torrents) || []; });
                });
            }
            return api.searchTorrents(pickerSearchBody(p, 'simple', p.anime.title + ' ' + pad2(p.episodeNumber)))
                .then(function (d2) { return (d2 && d2.torrents) || []; });
        }).then(function (list) {
            if (!state.picker || p.seq !== seq) return;
            p.torrents = list.slice().sort(function (a, b) {
                return ((b.isBestRelease ? 1 : 0) - (a.isBestRelease ? 1 : 0)) || ((b.seeders || 0) - (a.seeders || 0));
            }).slice(0, 60);
            p.loading = false;
            renderPicker();
        }).catch(function (e) {
            if (!state.picker || p.seq !== seq) return;
            console.error('[Torrents] search failed:', e);
            p.loading = false;
            p.error = (e && e.message) || 'The search failed.';
            renderPicker();
        });
    }

    function formatBytes(n) {
        if (!n) return '';
        var u = ['B', 'KB', 'MB', 'GB', 'TB'], i = 0;
        while (n >= 1024 && i < u.length - 1) { n /= 1024; i++; }
        return (i >= 3 ? n.toFixed(2) : Math.round(n)) + ' ' + u[i];
    }

    function renderPicker() {
        var p = state.picker;
        if (!p) return;
        var box = $('#picker-list');
        box.innerHTML = '';
        $('#picker-title').textContent = p.step === 'files' ? 'Choose the file to play' : 'Choose a torrent';
        $('#picker-sub').textContent = p.anime.title + ' \u2014 Episode ' + p.episodeNumber;

        function note(text) {
            var n = document.createElement('p');
            n.className = 'empty-note';
            n.textContent = text;
            box.appendChild(n);
        }
        function row(cls, activate) {
            var r = document.createElement('div');
            r.className = 'picker-row ' + cls;
            r.tabIndex = 0;
            r._activate = activate;
            r.addEventListener('click', activate);
            box.appendChild(r);
            return r;
        }
        function badge(parent, text, good) {
            var b = document.createElement('span');
            b.className = 'pr-badge' + (good ? ' good' : '');
            b.textContent = text;
            parent.appendChild(b);
        }
        var focusEl = null, likelyEl = null;

        if (p.step === 'results') {
            var mode = row('picker-mode', toggleBatch);
            mode._mode = true;
            mode.innerHTML = '<span class="pr-name">Show</span><span class="setting-value"><span class="set-arrow">' + CHEV_L +
                '</span><span class="set-val"></span><span class="set-arrow">' + CHEV_R + '</span></span>';
            mode.querySelector('.set-val').textContent = p.batch ? 'Batches' : 'Single episodes';
            focusEl = mode;
            if (p.loading) note('Searching\u2026');
            else if (p.error) note('Search failed: ' + p.error);
            else if (!p.torrents.length) note('No torrents found. Check that a torrent provider is installed in Seanime, or try Batches.');
            p.torrents.forEach(function (t) {
                var r = row('picker-torrent', function () { pickTorrent(t); });
                var name = document.createElement('div');
                name.className = 'pr-name';
                name.textContent = t.name;
                var meta = document.createElement('div');
                meta.className = 'pr-meta';
                var bits = [];
                var size = t.formattedSize || formatBytes(t.size);
                if (size) bits.push(size);
                bits.push((t.seeders || 0) + ' seeders');
                if (t.resolution) bits.push(t.resolution);
                if (t.releaseGroup) bits.push(t.releaseGroup);
                var when = formatAirDate(t.date);
                if (when) bits.push(when);
                meta.textContent = bits.join('  \u00B7  ');
                if (t.isBestRelease) badge(meta, 'Best release', true);
                if (t.isBatch) badge(meta, 'Batch');
                r.appendChild(name); r.appendChild(meta);
                if (focusEl && focusEl._mode) focusEl = r;      // start on the first torrent, not on the filter row
            });
        } else {
            if (p.loading) note('Reading the torrent\u2026');
            else if (p.error) note('Could not read the torrent: ' + p.error);
            else if (!p.files.length) note('No playable files found in this torrent.');
            p.files.forEach(function (f) {
                var r = row('picker-torrent', function () { startManualTorrent(p.torrent, f.index); });
                var name = document.createElement('div');
                name.className = 'pr-name';
                name.textContent = f.displayTitle || f.displayPath || f.path;
                var meta = document.createElement('div');
                meta.className = 'pr-meta';
                meta.textContent = f.episodeNumber ? 'Episode ' + f.episodeNumber : (f.displayPath || '');
                if (f.isLikely) badge(meta, 'Likely match', true);
                r.appendChild(name); r.appendChild(meta);
                if (f.isLikely && !likelyEl) likelyEl = r;
                if (!focusEl) focusEl = r;
            });
            if (likelyEl) focusEl = likelyEl;          // start on the file that matches the episode
        }
        if (focusEl) { try { focusEl.focus(); } catch (e) {} }
    }

    function toggleBatch() {
        var p = state.picker;
        if (!p) return;
        p.batch = !p.batch;
        runTorrentSearch();
    }

    function pickTorrent(t) {
        var p = state.picker;
        if (!p) return;
        if (!t.isBatch) { startManualTorrent(t, null); return; }
        p.torrent = t; p.step = 'files'; p.loading = true; p.error = ''; p.files = [];
        var seq = ++p.seq;
        renderPicker();
        api.getTorrentFilePreviews(t, p.episodeNumber, baseMediaFor(p.anime)).then(function (files) {
            if (!state.picker || p.seq !== seq) return;
            p.files = files || [];
            p.loading = false;
            renderPicker();
        }).catch(function (e) {
            if (!state.picker || p.seq !== seq) return;
            p.loading = false;
            p.error = (e && e.message) || 'Unknown error';
            renderPicker();
        });
    }

    function startManualTorrent(torrent, fileIndex) {
        var p = state.picker;
        if (!p) return;
        state.picker = null;
        $('#torrent-picker').classList.add('hidden');
        state.currentAnime = p.anime;
        startPlayback({ kind: 'torrent', anime: p.anime, episodeNumber: p.episodeNumber, aniDb: p.aniDb,
                        torrent: torrent, fileIndex: fileIndex });
    }

    function openPickerForEpisode(index) {
        var d = state.detail;
        if (!d) return;
        var ep = detailEpisodes()[index];
        if (!ep) return;
        state.playbackOrigin = 'detail';
        state.currentAnime = d.anime;
        openTorrentPicker(d.anime, ep.episodeNumber || ep.number || (index + 1), ep.aniDBEpisode || null, false);
    }

    function handlePickerKeys(keyCode, e) {
        var K = KEY_CODES, p = state.picker;
        var rows = $('#picker-list').querySelectorAll('.picker-row');
        var at = -1;
        for (var i = 0; i < rows.length; i++) if (rows[i] === document.activeElement) at = i;
        if (keyCode === K.UP || keyCode === K.DOWN) {
            e.preventDefault();
            var next = Math.max(0, Math.min(rows.length - 1, at < 0 ? 0 : at + (keyCode === K.DOWN ? 1 : -1)));
            if (rows[next]) rows[next].focus();
        } else if ((keyCode === K.LEFT || keyCode === K.RIGHT) && at >= 0 && rows[at]._mode) {
            e.preventDefault();
            toggleBatch();
        } else if (keyCode === K.ENTER && at >= 0) {
            e.preventDefault();
            rows[at]._activate();
        } else if (keyCode === K.RETURN) {
            if (p.step === 'files') { p.step = 'results'; renderPicker(); }
            else closeTorrentPicker();
        } else {
            e.preventDefault();
        }
    }

    // ===== Boot =====
    function boot() {
        if (booted) return;
        booted = true;
        DEBUG && console.log('[Boot] Seanime TV starting...');

        try {
            document.addEventListener('keydown', handleKeyDown);

            function updateClock() {
                var now = new Date();
                var el = $('#header-time');
                if (el) {
                    var hh = String(now.getHours());
                    var mm = String(now.getMinutes());
                    if (hh.length < 2) hh = '0' + hh;
                    if (mm.length < 2) mm = '0' + mm;
                    el.textContent = hh + ':' + mm;
                }
            }
            updateClock();
            setInterval(updateClock, 10000);

            var urlInput = $('#server-url-input');
            var pwInput = $('#server-password-input');
            var connectBtn = $('#connect-btn');
            var logoutBtn = $('#logout-btn');

            urlInput.addEventListener('keydown', function (e) {
                if (e.keyCode === KEY_CODES.DOWN) { e.preventDefault(); hideIME(); pwInput.focus(); }
                else if (e.keyCode === KEY_CODES.ENTER) { e.preventDefault(); connectBtn.click(); }
            });
            urlInput.addEventListener('focus', function () { urlInput.select(); showIME(); });

            pwInput.addEventListener('keydown', function (e) {
                if (e.keyCode === KEY_CODES.UP) { e.preventDefault(); urlInput.focus(); }
                else if (e.keyCode === KEY_CODES.DOWN) { e.preventDefault(); hideIME(); connectBtn.focus(); }
                else if (e.keyCode === KEY_CODES.ENTER) { e.preventDefault(); connectBtn.click(); }
            });
            pwInput.addEventListener('focus', function () { pwInput.select(); showIME(); });

            connectBtn.addEventListener('keydown', function (e) {
                if (e.keyCode === KEY_CODES.UP) { e.preventDefault(); pwInput.focus(); }
                else if (e.keyCode === KEY_CODES.ENTER) { e.preventDefault(); connectBtn.click(); }
            });

            connectBtn.addEventListener('click', function () {
                var url = urlInput.value.trim();
                var password = pwInput.value.trim();
                if (!url) { $('#setup-error').textContent = 'Please enter a server address'; return; }
                url = normalizeServerUrl(url);
                if (!/^https?:\/\/[^\/]+/i.test(url)) { $('#setup-error').textContent = 'Enter a valid address, e.g. http://192.168.1.100:43211'; return; }
                $('#setup-error').textContent = '';
                connectBtn.textContent = 'Connecting...';
                showScreen('loading');
                login(url, password).then(function () {
                    hideIME();
                    showScreen('home');
                    return loadLibrary();
                }).then(function () {
                    setTimeout(function () {
                        var btn = $('#hero-play-btn');
                        if (btn && btn.style.display !== 'none') btn.focus();
                    }, 100);
                }).catch(function (e) {
                    $('#setup-error').textContent = e.message || 'Connection failed';
                    connectBtn.textContent = 'Connect';
                    showScreen('setup');
                });
            });

            logoutBtn.addEventListener('click', function () { logout(); });
            logoutBtn.addEventListener('keydown', function (e) {
                if (e.keyCode === KEY_CODES.ENTER) { e.preventDefault(); logout(); }
            });

            var searchBox = $('#header-search');
            var searchInput = $('#search-input');
            var searchBtn = $('#search-btn');
            var navHome = $('#nav-home');
            var navDiscover = $('#nav-discover');
            var navSchedule = $('#nav-schedule');
            var navQueue = $('#nav-queue');
            var navProfile = $('#nav-profile');
            var settingsBtn = $('#settings-btn');

            function focusBelowHeader() {
                var target = null;
                if (state.view === 'discover') {
                    target = document.querySelector('#discover-rows .anime-card');
                } else if (state.view === 'schedule') {
                    target = document.querySelector('#schedule-rows .schedule-card:not(.aired)') || document.querySelector('#schedule-rows .anime-card');
                } else {
                    target = (searchBox && $('#search-section').style.display !== 'none' &&
                              document.querySelector('#search-results-row .anime-card')) ||
                             (($('#hero-play-btn').style.display !== 'none') && $('#hero-play-btn')) ||
                             document.querySelector('#content-area .anime-card');
                }
                if (target) target.focus();
            }

            // left-to-right order of everything focusable in the header
            var headerOrder = [navHome, navDiscover, navSchedule, navQueue, navProfile, searchInput, searchBtn, settingsBtn, logoutBtn];
            function moveHeaderFocus(from, delta) {
                var next = headerOrder[headerOrder.indexOf(from) + delta];
                if (next) next.focus();
            }
            headerOrder.forEach(function (el) {
                if (el === searchInput) return;
                el.addEventListener('keydown', function (e) {
                    if (e.keyCode === KEY_CODES.LEFT) { e.preventDefault(); moveHeaderFocus(el, -1); }
                    else if (e.keyCode === KEY_CODES.RIGHT) { e.preventDefault(); moveHeaderFocus(el, 1); }
                    else if (e.keyCode === KEY_CODES.DOWN) { e.preventDefault(); focusBelowHeader(); }
                    else if (e.keyCode === KEY_CODES.ENTER && el !== logoutBtn) { e.preventDefault(); el.click(); }
                });
            });

            searchInput.addEventListener('focus', function () { searchBox.classList.add('focused'); });
            searchInput.addEventListener('blur', function () { searchBox.classList.remove('focused'); });
            searchInput.addEventListener('keydown', function (e) {
                // 65376 = Tizen IME "Done" key
                if (e.keyCode === 65376) { e.preventDefault(); runSearch(); }
                else if (e.keyCode === KEY_CODES.DOWN) { e.preventDefault(); hideIME(); focusBelowHeader(); }
                else if (e.keyCode === KEY_CODES.RIGHT && searchInput.selectionStart === searchInput.value.length) {
                    e.preventDefault(); moveHeaderFocus(searchInput, 1);
                }
                else if (e.keyCode === KEY_CODES.LEFT && searchInput.selectionEnd === 0) {
                    e.preventDefault(); moveHeaderFocus(searchInput, -1);
                }
            });

            searchBtn.addEventListener('click', runSearch);
            navHome.addEventListener('click', function () { setView('home'); });
            navDiscover.addEventListener('click', function () { setView('discover'); });
            navSchedule.addEventListener('click', function () { setView('schedule'); });
            navQueue.addEventListener('click', function () { setView('queue'); });
            navProfile.addEventListener('click', function () { setView('profile'); });
            settingsBtn.addEventListener('click', openSettings);

            applySubtitleStyle();

            $('#ctrl-play-pause').addEventListener('click', togglePlayPause);
            $('#ctrl-rewind').addEventListener('click', function () { avplaySeekRelative(-10000); });
            $('#ctrl-forward').addEventListener('click', function () { avplaySeekRelative(10000); });
            $('#ctrl-stop').addEventListener('click', function () { stopPlayback(); leavePlayer(); });
            $('#ctrl-audio').addEventListener('click', function () { openTrackPanel('audio'); });
            $('#ctrl-subs').addEventListener('click', function () { openTrackPanel('text'); });
            $('#ctrl-speed').addEventListener('click', function () { openTrackPanel('speed'); });
            $('#skip-btn').addEventListener('click', skipNow);
            $('#detail-play').addEventListener('click', playDetailTarget);
            $('#detail-list').addEventListener('click', openListPanel);
            $('#player-error-retry').addEventListener('click', retryPlayback);
            $('#player-error-pick').addEventListener('click', function () {
                var ctx = state.lastPlayback;
                if (!ctx) return;
                hidePlayerError();
                openTorrentPicker(ctx.anime, ctx.episodeNumber, ctx.aniDb, true);
            });
            $('#player-error-back').addEventListener('click', function () { stopPlayback(); leavePlayer(); });
            $('#ctrl-prev').addEventListener('click', function () { playRelativeEpisode(-1); });
            $('#ctrl-next').addEventListener('click', function () { playRelativeEpisode(1); });
            $('#player-screen').addEventListener('mousemove', function () {
                if (state.currentScreen === 'player') showControls();
            });

            // Auto-login
            var savedUrl = localStorage.getItem(STORAGE_KEYS.SERVER_URL);
            var savedHash = credGet(STORAGE_KEYS.PASSWORD_HASH) || '';
            if (isSetupComplete() && savedUrl) {
                DEBUG && console.log('[Session] Auto-login with saved server:', savedUrl);
                var lt = $('#loading-text');
                if (lt) lt.textContent = 'Reconnecting to ' + savedUrl + '...';
                showScreen('loading');
                login(savedUrl, null, savedHash).then(function () {
                    showScreen('home');
                    return loadLibrary();
                }).then(function () {
                    setTimeout(function () {
                        var btn = $('#hero-play-btn');
                        if (btn && btn.style.display !== 'none') btn.focus();
                    }, 100);
                }).catch(function (e) {
                    console.warn('[Session] Auto-login failed:', e.message);
                    var errEl = $('#setup-error');
                    if (errEl) errEl.textContent = 'Auto-login failed: ' + e.message;
                    openSetupScreen();
                });
            } else {
                DEBUG && console.log('[Session] First-time setup');
                openSetupScreen();
            }

            DEBUG && console.log('[Boot] Ready.');
        } catch (err) {
            console.error('[Boot] Failed:', err);
            var setup = document.getElementById('setup-screen');
            var loading = document.getElementById('loading-screen');
            if (loading) loading.classList.remove('active');
            if (setup) setup.classList.add('active');
            var errEl = document.getElementById('setup-error');
            if (errEl) errEl.textContent = 'Init error: ' + err.message;
        }
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', boot);
    } else {
        boot();
    }
    window.addEventListener('load', boot);

    // Test hook (only active when a test harness sets window.__SEANIME_TEST__ first).
    if (window.__SEANIME_TEST__) {
        window.__seanime = {
            CONFIG: CONFIG, state: state, api: api, sha256: sha256,
            normalizeServerUrl: normalizeServerUrl, wsBaseUrl: wsBaseUrl, buildWsVariants: buildWsVariants,
            rewriteStreamUrl: rewriteStreamUrl, credGet: credGet, STORAGE_KEYS: STORAGE_KEYS,
            makeHmacToken: makeHmacToken, buildLocalStreamUrl: buildLocalStreamUrl, hmacSha256Bin: hmacSha256Bin, b64url: b64url,
            describeTorrentError: describeTorrentError, describeAvError: describeAvError,
            startPlayback: startPlayback, failPlayback: failPlayback, playEpisodeAuto: playEpisodeAuto,
            openAnimeDetail: openAnimeDetail, renderEpisodeList: renderEpisodeList, normalizeScore: normalizeScore, cleanDescription: cleanDescription,
            lazyImage: lazyImage, normalizeAnime: normalizeAnime, normalizeContinueWatching: normalizeContinueWatching,
            parseSubtitles: parseSubtitles, cueTextAt: cueTextAt, loadTracks: loadTracks, selectTrack: selectTrack, applyTrackPreferences: applyTrackPreferences, openTrackPanel: openTrackPanel,
            openTorrentPicker: openTorrentPicker, openPickerForEpisode: openPickerForEpisode, groupSchedule: groupSchedule, renderSchedule: renderSchedule, loadSchedule: loadSchedule, setView: setView, renderPlayerError: renderPlayerError,
            mergeEpisodes: mergeEpisodes, loadEpisodeBundle: loadEpisodeBundle, showBuffering: showBuffering,
            onSubtitleChange: onSubtitleChange, cleanSubtitleText: cleanSubtitleText, pickDefaultSubtitle: pickDefaultSubtitle,
            startAppSubs: startAppSubs, readTracks: readTracks, getSetting: getSetting,
            showControls: showControls, hideControls: hideControls, controlsShown: controlsShown, paintProgress: paintProgress, startProgressTracking: startProgressTracking,
            handlePlayerKeys: handlePlayerKeys, scrubStep: scrubStep, commitScrub: commitScrub, cancelScrub: cancelScrub, seekAbsolute: seekAbsolute,
            applyPlaybackSpeed: applyPlaybackSpeed, updateSkipPrompt: updateSkipPrompt, skipNow: skipNow, currentSkipSegments: currentSkipSegments,
            chaptersToSegments: chaptersToSegments, mkvFindChapters: mkvFindChapters, fetchAniSkip: fetchAniSkip, loadSkipSegments: loadSkipSegments,
            handleWsTorrentEvent: handleWsTorrentEvent, applyTorrentFeedback: applyTorrentFeedback, renderTorrentFeedback: renderTorrentFeedback,
            showTorrentLoadingOverlay: showTorrentLoadingOverlay, hideTorrentLoadingOverlay: hideTorrentLoadingOverlay, bufferingLabel: bufferingLabel, setSetting: setSetting,
            tryTranscodeFallback: tryTranscodeFallback, requestTranscodeUrl: requestTranscodeUrl, onAvError: onAvError, stopPlayback: stopPlayback,
            isCodecFailure: isCodecFailure, avErrorText: avErrorText, describeTranscodeError: describeTranscodeError
        };
    }

})();
