import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound42
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1344 : keyMomentRows (1344 : Fin 2886) =
    keyMomentRow1344 := by decide +kernel

theorem keyMomentRowsAt1345 : keyMomentRows (1345 : Fin 2886) =
    keyMomentRow1345 := by decide +kernel

theorem keyMomentRowsAt1346 : keyMomentRows (1346 : Fin 2886) =
    keyMomentRow1346 := by decide +kernel

theorem keyMomentRowsAt1347 : keyMomentRows (1347 : Fin 2886) =
    keyMomentRow1347 := by decide +kernel

theorem keyMomentRowsAt1348 : keyMomentRows (1348 : Fin 2886) =
    keyMomentRow1348 := by decide +kernel

theorem keyMomentRowsAt1349 : keyMomentRows (1349 : Fin 2886) =
    keyMomentRow1349 := by decide +kernel

theorem keyMomentRowsAt1350 : keyMomentRows (1350 : Fin 2886) =
    keyMomentRow1350 := by decide +kernel

theorem keyMomentRowsAt1351 : keyMomentRows (1351 : Fin 2886) =
    keyMomentRow1351 := by decide +kernel

theorem keyMomentRowsAt1352 : keyMomentRows (1352 : Fin 2886) =
    keyMomentRow1352 := by decide +kernel

theorem keyMomentRowsAt1353 : keyMomentRows (1353 : Fin 2886) =
    keyMomentRow1353 := by decide +kernel

theorem keyMomentRowsAt1354 : keyMomentRows (1354 : Fin 2886) =
    keyMomentRow1354 := by decide +kernel

theorem keyMomentRowsAt1355 : keyMomentRows (1355 : Fin 2886) =
    keyMomentRow1355 := by decide +kernel

theorem keyMomentRowsAt1356 : keyMomentRows (1356 : Fin 2886) =
    keyMomentRow1356 := by decide +kernel

theorem keyMomentRowsAt1357 : keyMomentRows (1357 : Fin 2886) =
    keyMomentRow1357 := by decide +kernel

theorem keyMomentRowsAt1358 : keyMomentRows (1358 : Fin 2886) =
    keyMomentRow1358 := by decide +kernel

theorem keyMomentRowsAt1359 : keyMomentRows (1359 : Fin 2886) =
    keyMomentRow1359 := by decide +kernel

theorem keyMomentRowsAt1360 : keyMomentRows (1360 : Fin 2886) =
    keyMomentRow1360 := by decide +kernel

theorem keyMomentRowsAt1361 : keyMomentRows (1361 : Fin 2886) =
    keyMomentRow1361 := by decide +kernel

theorem keyMomentRowsAt1362 : keyMomentRows (1362 : Fin 2886) =
    keyMomentRow1362 := by decide +kernel

theorem keyMomentRowsAt1363 : keyMomentRows (1363 : Fin 2886) =
    keyMomentRow1363 := by decide +kernel

theorem keyMomentRowsAt1364 : keyMomentRows (1364 : Fin 2886) =
    keyMomentRow1364 := by decide +kernel

theorem keyMomentRowsAt1365 : keyMomentRows (1365 : Fin 2886) =
    keyMomentRow1365 := by decide +kernel

theorem keyMomentRowsAt1366 : keyMomentRows (1366 : Fin 2886) =
    keyMomentRow1366 := by decide +kernel

theorem keyMomentRowsAt1367 : keyMomentRows (1367 : Fin 2886) =
    keyMomentRow1367 := by decide +kernel

theorem keyMomentRowsAt1368 : keyMomentRows (1368 : Fin 2886) =
    keyMomentRow1368 := by decide +kernel

theorem keyMomentRowsAt1369 : keyMomentRows (1369 : Fin 2886) =
    keyMomentRow1369 := by decide +kernel

theorem keyMomentRowsAt1370 : keyMomentRows (1370 : Fin 2886) =
    keyMomentRow1370 := by decide +kernel

theorem keyMomentRowsAt1371 : keyMomentRows (1371 : Fin 2886) =
    keyMomentRow1371 := by decide +kernel

theorem keyMomentRowsAt1372 : keyMomentRows (1372 : Fin 2886) =
    keyMomentRow1372 := by decide +kernel

theorem keyMomentRowsAt1373 : keyMomentRows (1373 : Fin 2886) =
    keyMomentRow1373 := by decide +kernel

theorem keyMomentRowsAt1374 : keyMomentRows (1374 : Fin 2886) =
    keyMomentRow1374 := by decide +kernel

theorem keyMomentRowsAt1375 : keyMomentRows (1375 : Fin 2886) =
    keyMomentRow1375 := by decide +kernel

theorem keyMomentChunkSound42 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 42) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1344 ∨ k.val = 1345 ∨ k.val = 1346 ∨ k.val = 1347 ∨ k.val = 1348 ∨ k.val = 1349 ∨ k.val = 1350 ∨ k.val = 1351 ∨ k.val = 1352 ∨ k.val = 1353 ∨ k.val = 1354 ∨ k.val = 1355 ∨ k.val = 1356 ∨ k.val = 1357 ∨ k.val = 1358 ∨ k.val = 1359 ∨ k.val = 1360 ∨ k.val = 1361 ∨ k.val = 1362 ∨ k.val = 1363 ∨ k.val = 1364 ∨ k.val = 1365 ∨ k.val = 1366 ∨ k.val = 1367 ∨ k.val = 1368 ∨ k.val = 1369 ∨ k.val = 1370 ∨ k.val = 1371 ∨ k.val = 1372 ∨ k.val = 1373 ∨ k.val = 1374 ∨ k.val = 1375 := by omega
  rcases heq with h1344 | h1345 | h1346 | h1347 | h1348 | h1349 | h1350 | h1351 | h1352 | h1353 | h1354 | h1355 | h1356 | h1357 | h1358 | h1359 | h1360 | h1361 | h1362 | h1363 | h1364 | h1365 | h1366 | h1367 | h1368 | h1369 | h1370 | h1371 | h1372 | h1373 | h1374 | h1375
  · have he : k = (1344 : Fin 2886) := Fin.ext h1344
    subst k
    rw [keyMomentRowsAt1344]
    exact keyMoment1344 B hB
  · have he : k = (1345 : Fin 2886) := Fin.ext h1345
    subst k
    rw [keyMomentRowsAt1345]
    exact keyMoment1345 B hB
  · have he : k = (1346 : Fin 2886) := Fin.ext h1346
    subst k
    rw [keyMomentRowsAt1346]
    exact keyMoment1346 B hB
  · have he : k = (1347 : Fin 2886) := Fin.ext h1347
    subst k
    rw [keyMomentRowsAt1347]
    exact keyMoment1347 B hB
  · have he : k = (1348 : Fin 2886) := Fin.ext h1348
    subst k
    rw [keyMomentRowsAt1348]
    exact keyMoment1348 B hB
  · have he : k = (1349 : Fin 2886) := Fin.ext h1349
    subst k
    rw [keyMomentRowsAt1349]
    exact keyMoment1349 B hB
  · have he : k = (1350 : Fin 2886) := Fin.ext h1350
    subst k
    rw [keyMomentRowsAt1350]
    exact keyMoment1350 B hB
  · have he : k = (1351 : Fin 2886) := Fin.ext h1351
    subst k
    rw [keyMomentRowsAt1351]
    exact keyMoment1351 B hB
  · have he : k = (1352 : Fin 2886) := Fin.ext h1352
    subst k
    rw [keyMomentRowsAt1352]
    exact keyMoment1352 B hB
  · have he : k = (1353 : Fin 2886) := Fin.ext h1353
    subst k
    rw [keyMomentRowsAt1353]
    exact keyMoment1353 B hB
  · have he : k = (1354 : Fin 2886) := Fin.ext h1354
    subst k
    rw [keyMomentRowsAt1354]
    exact keyMoment1354 B hB
  · have he : k = (1355 : Fin 2886) := Fin.ext h1355
    subst k
    rw [keyMomentRowsAt1355]
    exact keyMoment1355 B hB
  · have he : k = (1356 : Fin 2886) := Fin.ext h1356
    subst k
    rw [keyMomentRowsAt1356]
    exact keyMoment1356 B hB
  · have he : k = (1357 : Fin 2886) := Fin.ext h1357
    subst k
    rw [keyMomentRowsAt1357]
    exact keyMoment1357 B hB
  · have he : k = (1358 : Fin 2886) := Fin.ext h1358
    subst k
    rw [keyMomentRowsAt1358]
    exact keyMoment1358 B hB
  · have he : k = (1359 : Fin 2886) := Fin.ext h1359
    subst k
    rw [keyMomentRowsAt1359]
    exact keyMoment1359 B hB
  · have he : k = (1360 : Fin 2886) := Fin.ext h1360
    subst k
    rw [keyMomentRowsAt1360]
    exact keyMoment1360 B hB
  · have he : k = (1361 : Fin 2886) := Fin.ext h1361
    subst k
    rw [keyMomentRowsAt1361]
    exact keyMoment1361 B hB
  · have he : k = (1362 : Fin 2886) := Fin.ext h1362
    subst k
    rw [keyMomentRowsAt1362]
    exact keyMoment1362 B hB
  · have he : k = (1363 : Fin 2886) := Fin.ext h1363
    subst k
    rw [keyMomentRowsAt1363]
    exact keyMoment1363 B hB
  · have he : k = (1364 : Fin 2886) := Fin.ext h1364
    subst k
    rw [keyMomentRowsAt1364]
    exact keyMoment1364 B hB
  · have he : k = (1365 : Fin 2886) := Fin.ext h1365
    subst k
    rw [keyMomentRowsAt1365]
    exact keyMoment1365 B hB
  · have he : k = (1366 : Fin 2886) := Fin.ext h1366
    subst k
    rw [keyMomentRowsAt1366]
    exact keyMoment1366 B hB
  · have he : k = (1367 : Fin 2886) := Fin.ext h1367
    subst k
    rw [keyMomentRowsAt1367]
    exact keyMoment1367 B hB
  · have he : k = (1368 : Fin 2886) := Fin.ext h1368
    subst k
    rw [keyMomentRowsAt1368]
    exact keyMoment1368 B hB
  · have he : k = (1369 : Fin 2886) := Fin.ext h1369
    subst k
    rw [keyMomentRowsAt1369]
    exact keyMoment1369 B hB
  · have he : k = (1370 : Fin 2886) := Fin.ext h1370
    subst k
    rw [keyMomentRowsAt1370]
    exact keyMoment1370 B hB
  · have he : k = (1371 : Fin 2886) := Fin.ext h1371
    subst k
    rw [keyMomentRowsAt1371]
    exact keyMoment1371 B hB
  · have he : k = (1372 : Fin 2886) := Fin.ext h1372
    subst k
    rw [keyMomentRowsAt1372]
    exact keyMoment1372 B hB
  · have he : k = (1373 : Fin 2886) := Fin.ext h1373
    subst k
    rw [keyMomentRowsAt1373]
    exact keyMoment1373 B hB
  · have he : k = (1374 : Fin 2886) := Fin.ext h1374
    subst k
    rw [keyMomentRowsAt1374]
    exact keyMoment1374 B hB
  · have he : k = (1375 : Fin 2886) := Fin.ext h1375
    subst k
    rw [keyMomentRowsAt1375]
    exact keyMoment1375 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
