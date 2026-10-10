import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound40
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1280 : keyMomentRows (1280 : Fin 2886) =
    keyMomentRow1280 := by decide +kernel

theorem keyMomentRowsAt1281 : keyMomentRows (1281 : Fin 2886) =
    keyMomentRow1281 := by decide +kernel

theorem keyMomentRowsAt1282 : keyMomentRows (1282 : Fin 2886) =
    keyMomentRow1282 := by decide +kernel

theorem keyMomentRowsAt1283 : keyMomentRows (1283 : Fin 2886) =
    keyMomentRow1283 := by decide +kernel

theorem keyMomentRowsAt1284 : keyMomentRows (1284 : Fin 2886) =
    keyMomentRow1284 := by decide +kernel

theorem keyMomentRowsAt1285 : keyMomentRows (1285 : Fin 2886) =
    keyMomentRow1285 := by decide +kernel

theorem keyMomentRowsAt1286 : keyMomentRows (1286 : Fin 2886) =
    keyMomentRow1286 := by decide +kernel

theorem keyMomentRowsAt1287 : keyMomentRows (1287 : Fin 2886) =
    keyMomentRow1287 := by decide +kernel

theorem keyMomentRowsAt1288 : keyMomentRows (1288 : Fin 2886) =
    keyMomentRow1288 := by decide +kernel

theorem keyMomentRowsAt1289 : keyMomentRows (1289 : Fin 2886) =
    keyMomentRow1289 := by decide +kernel

theorem keyMomentRowsAt1290 : keyMomentRows (1290 : Fin 2886) =
    keyMomentRow1290 := by decide +kernel

theorem keyMomentRowsAt1291 : keyMomentRows (1291 : Fin 2886) =
    keyMomentRow1291 := by decide +kernel

theorem keyMomentRowsAt1292 : keyMomentRows (1292 : Fin 2886) =
    keyMomentRow1292 := by decide +kernel

theorem keyMomentRowsAt1293 : keyMomentRows (1293 : Fin 2886) =
    keyMomentRow1293 := by decide +kernel

theorem keyMomentRowsAt1294 : keyMomentRows (1294 : Fin 2886) =
    keyMomentRow1294 := by decide +kernel

theorem keyMomentRowsAt1295 : keyMomentRows (1295 : Fin 2886) =
    keyMomentRow1295 := by decide +kernel

theorem keyMomentRowsAt1296 : keyMomentRows (1296 : Fin 2886) =
    keyMomentRow1296 := by decide +kernel

theorem keyMomentRowsAt1297 : keyMomentRows (1297 : Fin 2886) =
    keyMomentRow1297 := by decide +kernel

theorem keyMomentRowsAt1298 : keyMomentRows (1298 : Fin 2886) =
    keyMomentRow1298 := by decide +kernel

theorem keyMomentRowsAt1299 : keyMomentRows (1299 : Fin 2886) =
    keyMomentRow1299 := by decide +kernel

theorem keyMomentRowsAt1300 : keyMomentRows (1300 : Fin 2886) =
    keyMomentRow1300 := by decide +kernel

theorem keyMomentRowsAt1301 : keyMomentRows (1301 : Fin 2886) =
    keyMomentRow1301 := by decide +kernel

theorem keyMomentRowsAt1302 : keyMomentRows (1302 : Fin 2886) =
    keyMomentRow1302 := by decide +kernel

theorem keyMomentRowsAt1303 : keyMomentRows (1303 : Fin 2886) =
    keyMomentRow1303 := by decide +kernel

theorem keyMomentRowsAt1304 : keyMomentRows (1304 : Fin 2886) =
    keyMomentRow1304 := by decide +kernel

theorem keyMomentRowsAt1305 : keyMomentRows (1305 : Fin 2886) =
    keyMomentRow1305 := by decide +kernel

theorem keyMomentRowsAt1306 : keyMomentRows (1306 : Fin 2886) =
    keyMomentRow1306 := by decide +kernel

theorem keyMomentRowsAt1307 : keyMomentRows (1307 : Fin 2886) =
    keyMomentRow1307 := by decide +kernel

theorem keyMomentRowsAt1308 : keyMomentRows (1308 : Fin 2886) =
    keyMomentRow1308 := by decide +kernel

theorem keyMomentRowsAt1309 : keyMomentRows (1309 : Fin 2886) =
    keyMomentRow1309 := by decide +kernel

theorem keyMomentRowsAt1310 : keyMomentRows (1310 : Fin 2886) =
    keyMomentRow1310 := by decide +kernel

theorem keyMomentRowsAt1311 : keyMomentRows (1311 : Fin 2886) =
    keyMomentRow1311 := by decide +kernel

theorem keyMomentChunkSound40 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 40) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1280 ∨ k.val = 1281 ∨ k.val = 1282 ∨ k.val = 1283 ∨ k.val = 1284 ∨ k.val = 1285 ∨ k.val = 1286 ∨ k.val = 1287 ∨ k.val = 1288 ∨ k.val = 1289 ∨ k.val = 1290 ∨ k.val = 1291 ∨ k.val = 1292 ∨ k.val = 1293 ∨ k.val = 1294 ∨ k.val = 1295 ∨ k.val = 1296 ∨ k.val = 1297 ∨ k.val = 1298 ∨ k.val = 1299 ∨ k.val = 1300 ∨ k.val = 1301 ∨ k.val = 1302 ∨ k.val = 1303 ∨ k.val = 1304 ∨ k.val = 1305 ∨ k.val = 1306 ∨ k.val = 1307 ∨ k.val = 1308 ∨ k.val = 1309 ∨ k.val = 1310 ∨ k.val = 1311 := by omega
  rcases heq with h1280 | h1281 | h1282 | h1283 | h1284 | h1285 | h1286 | h1287 | h1288 | h1289 | h1290 | h1291 | h1292 | h1293 | h1294 | h1295 | h1296 | h1297 | h1298 | h1299 | h1300 | h1301 | h1302 | h1303 | h1304 | h1305 | h1306 | h1307 | h1308 | h1309 | h1310 | h1311
  · have he : k = (1280 : Fin 2886) := Fin.ext h1280
    subst k
    rw [keyMomentRowsAt1280]
    exact keyMoment1280 B hB
  · have he : k = (1281 : Fin 2886) := Fin.ext h1281
    subst k
    rw [keyMomentRowsAt1281]
    exact keyMoment1281 B hB
  · have he : k = (1282 : Fin 2886) := Fin.ext h1282
    subst k
    rw [keyMomentRowsAt1282]
    exact keyMoment1282 B hB
  · have he : k = (1283 : Fin 2886) := Fin.ext h1283
    subst k
    rw [keyMomentRowsAt1283]
    exact keyMoment1283 B hB
  · have he : k = (1284 : Fin 2886) := Fin.ext h1284
    subst k
    rw [keyMomentRowsAt1284]
    exact keyMoment1284 B hB
  · have he : k = (1285 : Fin 2886) := Fin.ext h1285
    subst k
    rw [keyMomentRowsAt1285]
    exact keyMoment1285 B hB
  · have he : k = (1286 : Fin 2886) := Fin.ext h1286
    subst k
    rw [keyMomentRowsAt1286]
    exact keyMoment1286 B hB
  · have he : k = (1287 : Fin 2886) := Fin.ext h1287
    subst k
    rw [keyMomentRowsAt1287]
    exact keyMoment1287 B hB
  · have he : k = (1288 : Fin 2886) := Fin.ext h1288
    subst k
    rw [keyMomentRowsAt1288]
    exact keyMoment1288 B hB
  · have he : k = (1289 : Fin 2886) := Fin.ext h1289
    subst k
    rw [keyMomentRowsAt1289]
    exact keyMoment1289 B hB
  · have he : k = (1290 : Fin 2886) := Fin.ext h1290
    subst k
    rw [keyMomentRowsAt1290]
    exact keyMoment1290 B hB
  · have he : k = (1291 : Fin 2886) := Fin.ext h1291
    subst k
    rw [keyMomentRowsAt1291]
    exact keyMoment1291 B hB
  · have he : k = (1292 : Fin 2886) := Fin.ext h1292
    subst k
    rw [keyMomentRowsAt1292]
    exact keyMoment1292 B hB
  · have he : k = (1293 : Fin 2886) := Fin.ext h1293
    subst k
    rw [keyMomentRowsAt1293]
    exact keyMoment1293 B hB
  · have he : k = (1294 : Fin 2886) := Fin.ext h1294
    subst k
    rw [keyMomentRowsAt1294]
    exact keyMoment1294 B hB
  · have he : k = (1295 : Fin 2886) := Fin.ext h1295
    subst k
    rw [keyMomentRowsAt1295]
    exact keyMoment1295 B hB
  · have he : k = (1296 : Fin 2886) := Fin.ext h1296
    subst k
    rw [keyMomentRowsAt1296]
    exact keyMoment1296 B hB
  · have he : k = (1297 : Fin 2886) := Fin.ext h1297
    subst k
    rw [keyMomentRowsAt1297]
    exact keyMoment1297 B hB
  · have he : k = (1298 : Fin 2886) := Fin.ext h1298
    subst k
    rw [keyMomentRowsAt1298]
    exact keyMoment1298 B hB
  · have he : k = (1299 : Fin 2886) := Fin.ext h1299
    subst k
    rw [keyMomentRowsAt1299]
    exact keyMoment1299 B hB
  · have he : k = (1300 : Fin 2886) := Fin.ext h1300
    subst k
    rw [keyMomentRowsAt1300]
    exact keyMoment1300 B hB
  · have he : k = (1301 : Fin 2886) := Fin.ext h1301
    subst k
    rw [keyMomentRowsAt1301]
    exact keyMoment1301 B hB
  · have he : k = (1302 : Fin 2886) := Fin.ext h1302
    subst k
    rw [keyMomentRowsAt1302]
    exact keyMoment1302 B hB
  · have he : k = (1303 : Fin 2886) := Fin.ext h1303
    subst k
    rw [keyMomentRowsAt1303]
    exact keyMoment1303 B hB
  · have he : k = (1304 : Fin 2886) := Fin.ext h1304
    subst k
    rw [keyMomentRowsAt1304]
    exact keyMoment1304 B hB
  · have he : k = (1305 : Fin 2886) := Fin.ext h1305
    subst k
    rw [keyMomentRowsAt1305]
    exact keyMoment1305 B hB
  · have he : k = (1306 : Fin 2886) := Fin.ext h1306
    subst k
    rw [keyMomentRowsAt1306]
    exact keyMoment1306 B hB
  · have he : k = (1307 : Fin 2886) := Fin.ext h1307
    subst k
    rw [keyMomentRowsAt1307]
    exact keyMoment1307 B hB
  · have he : k = (1308 : Fin 2886) := Fin.ext h1308
    subst k
    rw [keyMomentRowsAt1308]
    exact keyMoment1308 B hB
  · have he : k = (1309 : Fin 2886) := Fin.ext h1309
    subst k
    rw [keyMomentRowsAt1309]
    exact keyMoment1309 B hB
  · have he : k = (1310 : Fin 2886) := Fin.ext h1310
    subst k
    rw [keyMomentRowsAt1310]
    exact keyMoment1310 B hB
  · have he : k = (1311 : Fin 2886) := Fin.ext h1311
    subst k
    rw [keyMomentRowsAt1311]
    exact keyMoment1311 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
