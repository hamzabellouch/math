import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound43
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1376 : keyMomentRows (1376 : Fin 2886) =
    keyMomentRow1376 := by decide +kernel

theorem keyMomentRowsAt1377 : keyMomentRows (1377 : Fin 2886) =
    keyMomentRow1377 := by decide +kernel

theorem keyMomentRowsAt1378 : keyMomentRows (1378 : Fin 2886) =
    keyMomentRow1378 := by decide +kernel

theorem keyMomentRowsAt1379 : keyMomentRows (1379 : Fin 2886) =
    keyMomentRow1379 := by decide +kernel

theorem keyMomentRowsAt1380 : keyMomentRows (1380 : Fin 2886) =
    keyMomentRow1380 := by decide +kernel

theorem keyMomentRowsAt1381 : keyMomentRows (1381 : Fin 2886) =
    keyMomentRow1381 := by decide +kernel

theorem keyMomentRowsAt1382 : keyMomentRows (1382 : Fin 2886) =
    keyMomentRow1382 := by decide +kernel

theorem keyMomentRowsAt1383 : keyMomentRows (1383 : Fin 2886) =
    keyMomentRow1383 := by decide +kernel

theorem keyMomentRowsAt1384 : keyMomentRows (1384 : Fin 2886) =
    keyMomentRow1384 := by decide +kernel

theorem keyMomentRowsAt1385 : keyMomentRows (1385 : Fin 2886) =
    keyMomentRow1385 := by decide +kernel

theorem keyMomentRowsAt1386 : keyMomentRows (1386 : Fin 2886) =
    keyMomentRow1386 := by decide +kernel

theorem keyMomentRowsAt1387 : keyMomentRows (1387 : Fin 2886) =
    keyMomentRow1387 := by decide +kernel

theorem keyMomentRowsAt1388 : keyMomentRows (1388 : Fin 2886) =
    keyMomentRow1388 := by decide +kernel

theorem keyMomentRowsAt1389 : keyMomentRows (1389 : Fin 2886) =
    keyMomentRow1389 := by decide +kernel

theorem keyMomentRowsAt1390 : keyMomentRows (1390 : Fin 2886) =
    keyMomentRow1390 := by decide +kernel

theorem keyMomentRowsAt1391 : keyMomentRows (1391 : Fin 2886) =
    keyMomentRow1391 := by decide +kernel

theorem keyMomentRowsAt1392 : keyMomentRows (1392 : Fin 2886) =
    keyMomentRow1392 := by decide +kernel

theorem keyMomentRowsAt1393 : keyMomentRows (1393 : Fin 2886) =
    keyMomentRow1393 := by decide +kernel

theorem keyMomentRowsAt1394 : keyMomentRows (1394 : Fin 2886) =
    keyMomentRow1394 := by decide +kernel

theorem keyMomentRowsAt1395 : keyMomentRows (1395 : Fin 2886) =
    keyMomentRow1395 := by decide +kernel

theorem keyMomentRowsAt1396 : keyMomentRows (1396 : Fin 2886) =
    keyMomentRow1396 := by decide +kernel

theorem keyMomentRowsAt1397 : keyMomentRows (1397 : Fin 2886) =
    keyMomentRow1397 := by decide +kernel

theorem keyMomentRowsAt1398 : keyMomentRows (1398 : Fin 2886) =
    keyMomentRow1398 := by decide +kernel

theorem keyMomentRowsAt1399 : keyMomentRows (1399 : Fin 2886) =
    keyMomentRow1399 := by decide +kernel

theorem keyMomentRowsAt1400 : keyMomentRows (1400 : Fin 2886) =
    keyMomentRow1400 := by decide +kernel

theorem keyMomentRowsAt1401 : keyMomentRows (1401 : Fin 2886) =
    keyMomentRow1401 := by decide +kernel

theorem keyMomentRowsAt1402 : keyMomentRows (1402 : Fin 2886) =
    keyMomentRow1402 := by decide +kernel

theorem keyMomentRowsAt1403 : keyMomentRows (1403 : Fin 2886) =
    keyMomentRow1403 := by decide +kernel

theorem keyMomentRowsAt1404 : keyMomentRows (1404 : Fin 2886) =
    keyMomentRow1404 := by decide +kernel

theorem keyMomentRowsAt1405 : keyMomentRows (1405 : Fin 2886) =
    keyMomentRow1405 := by decide +kernel

theorem keyMomentRowsAt1406 : keyMomentRows (1406 : Fin 2886) =
    keyMomentRow1406 := by decide +kernel

theorem keyMomentRowsAt1407 : keyMomentRows (1407 : Fin 2886) =
    keyMomentRow1407 := by decide +kernel

theorem keyMomentChunkSound43 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 43) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1376 ∨ k.val = 1377 ∨ k.val = 1378 ∨ k.val = 1379 ∨ k.val = 1380 ∨ k.val = 1381 ∨ k.val = 1382 ∨ k.val = 1383 ∨ k.val = 1384 ∨ k.val = 1385 ∨ k.val = 1386 ∨ k.val = 1387 ∨ k.val = 1388 ∨ k.val = 1389 ∨ k.val = 1390 ∨ k.val = 1391 ∨ k.val = 1392 ∨ k.val = 1393 ∨ k.val = 1394 ∨ k.val = 1395 ∨ k.val = 1396 ∨ k.val = 1397 ∨ k.val = 1398 ∨ k.val = 1399 ∨ k.val = 1400 ∨ k.val = 1401 ∨ k.val = 1402 ∨ k.val = 1403 ∨ k.val = 1404 ∨ k.val = 1405 ∨ k.val = 1406 ∨ k.val = 1407 := by omega
  rcases heq with h1376 | h1377 | h1378 | h1379 | h1380 | h1381 | h1382 | h1383 | h1384 | h1385 | h1386 | h1387 | h1388 | h1389 | h1390 | h1391 | h1392 | h1393 | h1394 | h1395 | h1396 | h1397 | h1398 | h1399 | h1400 | h1401 | h1402 | h1403 | h1404 | h1405 | h1406 | h1407
  · have he : k = (1376 : Fin 2886) := Fin.ext h1376
    subst k
    rw [keyMomentRowsAt1376]
    exact keyMoment1376 B hB
  · have he : k = (1377 : Fin 2886) := Fin.ext h1377
    subst k
    rw [keyMomentRowsAt1377]
    exact keyMoment1377 B hB
  · have he : k = (1378 : Fin 2886) := Fin.ext h1378
    subst k
    rw [keyMomentRowsAt1378]
    exact keyMoment1378 B hB
  · have he : k = (1379 : Fin 2886) := Fin.ext h1379
    subst k
    rw [keyMomentRowsAt1379]
    exact keyMoment1379 B hB
  · have he : k = (1380 : Fin 2886) := Fin.ext h1380
    subst k
    rw [keyMomentRowsAt1380]
    exact keyMoment1380 B hB
  · have he : k = (1381 : Fin 2886) := Fin.ext h1381
    subst k
    rw [keyMomentRowsAt1381]
    exact keyMoment1381 B hB
  · have he : k = (1382 : Fin 2886) := Fin.ext h1382
    subst k
    rw [keyMomentRowsAt1382]
    exact keyMoment1382 B hB
  · have he : k = (1383 : Fin 2886) := Fin.ext h1383
    subst k
    rw [keyMomentRowsAt1383]
    exact keyMoment1383 B hB
  · have he : k = (1384 : Fin 2886) := Fin.ext h1384
    subst k
    rw [keyMomentRowsAt1384]
    exact keyMoment1384 B hB
  · have he : k = (1385 : Fin 2886) := Fin.ext h1385
    subst k
    rw [keyMomentRowsAt1385]
    exact keyMoment1385 B hB
  · have he : k = (1386 : Fin 2886) := Fin.ext h1386
    subst k
    rw [keyMomentRowsAt1386]
    exact keyMoment1386 B hB
  · have he : k = (1387 : Fin 2886) := Fin.ext h1387
    subst k
    rw [keyMomentRowsAt1387]
    exact keyMoment1387 B hB
  · have he : k = (1388 : Fin 2886) := Fin.ext h1388
    subst k
    rw [keyMomentRowsAt1388]
    exact keyMoment1388 B hB
  · have he : k = (1389 : Fin 2886) := Fin.ext h1389
    subst k
    rw [keyMomentRowsAt1389]
    exact keyMoment1389 B hB
  · have he : k = (1390 : Fin 2886) := Fin.ext h1390
    subst k
    rw [keyMomentRowsAt1390]
    exact keyMoment1390 B hB
  · have he : k = (1391 : Fin 2886) := Fin.ext h1391
    subst k
    rw [keyMomentRowsAt1391]
    exact keyMoment1391 B hB
  · have he : k = (1392 : Fin 2886) := Fin.ext h1392
    subst k
    rw [keyMomentRowsAt1392]
    exact keyMoment1392 B hB
  · have he : k = (1393 : Fin 2886) := Fin.ext h1393
    subst k
    rw [keyMomentRowsAt1393]
    exact keyMoment1393 B hB
  · have he : k = (1394 : Fin 2886) := Fin.ext h1394
    subst k
    rw [keyMomentRowsAt1394]
    exact keyMoment1394 B hB
  · have he : k = (1395 : Fin 2886) := Fin.ext h1395
    subst k
    rw [keyMomentRowsAt1395]
    exact keyMoment1395 B hB
  · have he : k = (1396 : Fin 2886) := Fin.ext h1396
    subst k
    rw [keyMomentRowsAt1396]
    exact keyMoment1396 B hB
  · have he : k = (1397 : Fin 2886) := Fin.ext h1397
    subst k
    rw [keyMomentRowsAt1397]
    exact keyMoment1397 B hB
  · have he : k = (1398 : Fin 2886) := Fin.ext h1398
    subst k
    rw [keyMomentRowsAt1398]
    exact keyMoment1398 B hB
  · have he : k = (1399 : Fin 2886) := Fin.ext h1399
    subst k
    rw [keyMomentRowsAt1399]
    exact keyMoment1399 B hB
  · have he : k = (1400 : Fin 2886) := Fin.ext h1400
    subst k
    rw [keyMomentRowsAt1400]
    exact keyMoment1400 B hB
  · have he : k = (1401 : Fin 2886) := Fin.ext h1401
    subst k
    rw [keyMomentRowsAt1401]
    exact keyMoment1401 B hB
  · have he : k = (1402 : Fin 2886) := Fin.ext h1402
    subst k
    rw [keyMomentRowsAt1402]
    exact keyMoment1402 B hB
  · have he : k = (1403 : Fin 2886) := Fin.ext h1403
    subst k
    rw [keyMomentRowsAt1403]
    exact keyMoment1403 B hB
  · have he : k = (1404 : Fin 2886) := Fin.ext h1404
    subst k
    rw [keyMomentRowsAt1404]
    exact keyMoment1404 B hB
  · have he : k = (1405 : Fin 2886) := Fin.ext h1405
    subst k
    rw [keyMomentRowsAt1405]
    exact keyMoment1405 B hB
  · have he : k = (1406 : Fin 2886) := Fin.ext h1406
    subst k
    rw [keyMomentRowsAt1406]
    exact keyMoment1406 B hB
  · have he : k = (1407 : Fin 2886) := Fin.ext h1407
    subst k
    rw [keyMomentRowsAt1407]
    exact keyMoment1407 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
