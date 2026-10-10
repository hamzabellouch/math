import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound41
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1312 : keyMomentRows (1312 : Fin 2886) =
    keyMomentRow1312 := by decide +kernel

theorem keyMomentRowsAt1313 : keyMomentRows (1313 : Fin 2886) =
    keyMomentRow1313 := by decide +kernel

theorem keyMomentRowsAt1314 : keyMomentRows (1314 : Fin 2886) =
    keyMomentRow1314 := by decide +kernel

theorem keyMomentRowsAt1315 : keyMomentRows (1315 : Fin 2886) =
    keyMomentRow1315 := by decide +kernel

theorem keyMomentRowsAt1316 : keyMomentRows (1316 : Fin 2886) =
    keyMomentRow1316 := by decide +kernel

theorem keyMomentRowsAt1317 : keyMomentRows (1317 : Fin 2886) =
    keyMomentRow1317 := by decide +kernel

theorem keyMomentRowsAt1318 : keyMomentRows (1318 : Fin 2886) =
    keyMomentRow1318 := by decide +kernel

theorem keyMomentRowsAt1319 : keyMomentRows (1319 : Fin 2886) =
    keyMomentRow1319 := by decide +kernel

theorem keyMomentRowsAt1320 : keyMomentRows (1320 : Fin 2886) =
    keyMomentRow1320 := by decide +kernel

theorem keyMomentRowsAt1321 : keyMomentRows (1321 : Fin 2886) =
    keyMomentRow1321 := by decide +kernel

theorem keyMomentRowsAt1322 : keyMomentRows (1322 : Fin 2886) =
    keyMomentRow1322 := by decide +kernel

theorem keyMomentRowsAt1323 : keyMomentRows (1323 : Fin 2886) =
    keyMomentRow1323 := by decide +kernel

theorem keyMomentRowsAt1324 : keyMomentRows (1324 : Fin 2886) =
    keyMomentRow1324 := by decide +kernel

theorem keyMomentRowsAt1325 : keyMomentRows (1325 : Fin 2886) =
    keyMomentRow1325 := by decide +kernel

theorem keyMomentRowsAt1326 : keyMomentRows (1326 : Fin 2886) =
    keyMomentRow1326 := by decide +kernel

theorem keyMomentRowsAt1327 : keyMomentRows (1327 : Fin 2886) =
    keyMomentRow1327 := by decide +kernel

theorem keyMomentRowsAt1328 : keyMomentRows (1328 : Fin 2886) =
    keyMomentRow1328 := by decide +kernel

theorem keyMomentRowsAt1329 : keyMomentRows (1329 : Fin 2886) =
    keyMomentRow1329 := by decide +kernel

theorem keyMomentRowsAt1330 : keyMomentRows (1330 : Fin 2886) =
    keyMomentRow1330 := by decide +kernel

theorem keyMomentRowsAt1331 : keyMomentRows (1331 : Fin 2886) =
    keyMomentRow1331 := by decide +kernel

theorem keyMomentRowsAt1332 : keyMomentRows (1332 : Fin 2886) =
    keyMomentRow1332 := by decide +kernel

theorem keyMomentRowsAt1333 : keyMomentRows (1333 : Fin 2886) =
    keyMomentRow1333 := by decide +kernel

theorem keyMomentRowsAt1334 : keyMomentRows (1334 : Fin 2886) =
    keyMomentRow1334 := by decide +kernel

theorem keyMomentRowsAt1335 : keyMomentRows (1335 : Fin 2886) =
    keyMomentRow1335 := by decide +kernel

theorem keyMomentRowsAt1336 : keyMomentRows (1336 : Fin 2886) =
    keyMomentRow1336 := by decide +kernel

theorem keyMomentRowsAt1337 : keyMomentRows (1337 : Fin 2886) =
    keyMomentRow1337 := by decide +kernel

theorem keyMomentRowsAt1338 : keyMomentRows (1338 : Fin 2886) =
    keyMomentRow1338 := by decide +kernel

theorem keyMomentRowsAt1339 : keyMomentRows (1339 : Fin 2886) =
    keyMomentRow1339 := by decide +kernel

theorem keyMomentRowsAt1340 : keyMomentRows (1340 : Fin 2886) =
    keyMomentRow1340 := by decide +kernel

theorem keyMomentRowsAt1341 : keyMomentRows (1341 : Fin 2886) =
    keyMomentRow1341 := by decide +kernel

theorem keyMomentRowsAt1342 : keyMomentRows (1342 : Fin 2886) =
    keyMomentRow1342 := by decide +kernel

theorem keyMomentRowsAt1343 : keyMomentRows (1343 : Fin 2886) =
    keyMomentRow1343 := by decide +kernel

theorem keyMomentChunkSound41 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 41) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1312 ∨ k.val = 1313 ∨ k.val = 1314 ∨ k.val = 1315 ∨ k.val = 1316 ∨ k.val = 1317 ∨ k.val = 1318 ∨ k.val = 1319 ∨ k.val = 1320 ∨ k.val = 1321 ∨ k.val = 1322 ∨ k.val = 1323 ∨ k.val = 1324 ∨ k.val = 1325 ∨ k.val = 1326 ∨ k.val = 1327 ∨ k.val = 1328 ∨ k.val = 1329 ∨ k.val = 1330 ∨ k.val = 1331 ∨ k.val = 1332 ∨ k.val = 1333 ∨ k.val = 1334 ∨ k.val = 1335 ∨ k.val = 1336 ∨ k.val = 1337 ∨ k.val = 1338 ∨ k.val = 1339 ∨ k.val = 1340 ∨ k.val = 1341 ∨ k.val = 1342 ∨ k.val = 1343 := by omega
  rcases heq with h1312 | h1313 | h1314 | h1315 | h1316 | h1317 | h1318 | h1319 | h1320 | h1321 | h1322 | h1323 | h1324 | h1325 | h1326 | h1327 | h1328 | h1329 | h1330 | h1331 | h1332 | h1333 | h1334 | h1335 | h1336 | h1337 | h1338 | h1339 | h1340 | h1341 | h1342 | h1343
  · have he : k = (1312 : Fin 2886) := Fin.ext h1312
    subst k
    rw [keyMomentRowsAt1312]
    exact keyMoment1312 B hB
  · have he : k = (1313 : Fin 2886) := Fin.ext h1313
    subst k
    rw [keyMomentRowsAt1313]
    exact keyMoment1313 B hB
  · have he : k = (1314 : Fin 2886) := Fin.ext h1314
    subst k
    rw [keyMomentRowsAt1314]
    exact keyMoment1314 B hB
  · have he : k = (1315 : Fin 2886) := Fin.ext h1315
    subst k
    rw [keyMomentRowsAt1315]
    exact keyMoment1315 B hB
  · have he : k = (1316 : Fin 2886) := Fin.ext h1316
    subst k
    rw [keyMomentRowsAt1316]
    exact keyMoment1316 B hB
  · have he : k = (1317 : Fin 2886) := Fin.ext h1317
    subst k
    rw [keyMomentRowsAt1317]
    exact keyMoment1317 B hB
  · have he : k = (1318 : Fin 2886) := Fin.ext h1318
    subst k
    rw [keyMomentRowsAt1318]
    exact keyMoment1318 B hB
  · have he : k = (1319 : Fin 2886) := Fin.ext h1319
    subst k
    rw [keyMomentRowsAt1319]
    exact keyMoment1319 B hB
  · have he : k = (1320 : Fin 2886) := Fin.ext h1320
    subst k
    rw [keyMomentRowsAt1320]
    exact keyMoment1320 B hB
  · have he : k = (1321 : Fin 2886) := Fin.ext h1321
    subst k
    rw [keyMomentRowsAt1321]
    exact keyMoment1321 B hB
  · have he : k = (1322 : Fin 2886) := Fin.ext h1322
    subst k
    rw [keyMomentRowsAt1322]
    exact keyMoment1322 B hB
  · have he : k = (1323 : Fin 2886) := Fin.ext h1323
    subst k
    rw [keyMomentRowsAt1323]
    exact keyMoment1323 B hB
  · have he : k = (1324 : Fin 2886) := Fin.ext h1324
    subst k
    rw [keyMomentRowsAt1324]
    exact keyMoment1324 B hB
  · have he : k = (1325 : Fin 2886) := Fin.ext h1325
    subst k
    rw [keyMomentRowsAt1325]
    exact keyMoment1325 B hB
  · have he : k = (1326 : Fin 2886) := Fin.ext h1326
    subst k
    rw [keyMomentRowsAt1326]
    exact keyMoment1326 B hB
  · have he : k = (1327 : Fin 2886) := Fin.ext h1327
    subst k
    rw [keyMomentRowsAt1327]
    exact keyMoment1327 B hB
  · have he : k = (1328 : Fin 2886) := Fin.ext h1328
    subst k
    rw [keyMomentRowsAt1328]
    exact keyMoment1328 B hB
  · have he : k = (1329 : Fin 2886) := Fin.ext h1329
    subst k
    rw [keyMomentRowsAt1329]
    exact keyMoment1329 B hB
  · have he : k = (1330 : Fin 2886) := Fin.ext h1330
    subst k
    rw [keyMomentRowsAt1330]
    exact keyMoment1330 B hB
  · have he : k = (1331 : Fin 2886) := Fin.ext h1331
    subst k
    rw [keyMomentRowsAt1331]
    exact keyMoment1331 B hB
  · have he : k = (1332 : Fin 2886) := Fin.ext h1332
    subst k
    rw [keyMomentRowsAt1332]
    exact keyMoment1332 B hB
  · have he : k = (1333 : Fin 2886) := Fin.ext h1333
    subst k
    rw [keyMomentRowsAt1333]
    exact keyMoment1333 B hB
  · have he : k = (1334 : Fin 2886) := Fin.ext h1334
    subst k
    rw [keyMomentRowsAt1334]
    exact keyMoment1334 B hB
  · have he : k = (1335 : Fin 2886) := Fin.ext h1335
    subst k
    rw [keyMomentRowsAt1335]
    exact keyMoment1335 B hB
  · have he : k = (1336 : Fin 2886) := Fin.ext h1336
    subst k
    rw [keyMomentRowsAt1336]
    exact keyMoment1336 B hB
  · have he : k = (1337 : Fin 2886) := Fin.ext h1337
    subst k
    rw [keyMomentRowsAt1337]
    exact keyMoment1337 B hB
  · have he : k = (1338 : Fin 2886) := Fin.ext h1338
    subst k
    rw [keyMomentRowsAt1338]
    exact keyMoment1338 B hB
  · have he : k = (1339 : Fin 2886) := Fin.ext h1339
    subst k
    rw [keyMomentRowsAt1339]
    exact keyMoment1339 B hB
  · have he : k = (1340 : Fin 2886) := Fin.ext h1340
    subst k
    rw [keyMomentRowsAt1340]
    exact keyMoment1340 B hB
  · have he : k = (1341 : Fin 2886) := Fin.ext h1341
    subst k
    rw [keyMomentRowsAt1341]
    exact keyMoment1341 B hB
  · have he : k = (1342 : Fin 2886) := Fin.ext h1342
    subst k
    rw [keyMomentRowsAt1342]
    exact keyMoment1342 B hB
  · have he : k = (1343 : Fin 2886) := Fin.ext h1343
    subst k
    rw [keyMomentRowsAt1343]
    exact keyMoment1343 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
