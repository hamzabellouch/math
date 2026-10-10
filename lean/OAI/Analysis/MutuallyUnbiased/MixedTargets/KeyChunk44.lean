import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound44
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1408 : keyMomentRows (1408 : Fin 2886) =
    keyMomentRow1408 := by decide +kernel

theorem keyMomentRowsAt1409 : keyMomentRows (1409 : Fin 2886) =
    keyMomentRow1409 := by decide +kernel

theorem keyMomentRowsAt1410 : keyMomentRows (1410 : Fin 2886) =
    keyMomentRow1410 := by decide +kernel

theorem keyMomentRowsAt1411 : keyMomentRows (1411 : Fin 2886) =
    keyMomentRow1411 := by decide +kernel

theorem keyMomentRowsAt1412 : keyMomentRows (1412 : Fin 2886) =
    keyMomentRow1412 := by decide +kernel

theorem keyMomentRowsAt1413 : keyMomentRows (1413 : Fin 2886) =
    keyMomentRow1413 := by decide +kernel

theorem keyMomentRowsAt1414 : keyMomentRows (1414 : Fin 2886) =
    keyMomentRow1414 := by decide +kernel

theorem keyMomentRowsAt1415 : keyMomentRows (1415 : Fin 2886) =
    keyMomentRow1415 := by decide +kernel

theorem keyMomentRowsAt1416 : keyMomentRows (1416 : Fin 2886) =
    keyMomentRow1416 := by decide +kernel

theorem keyMomentRowsAt1417 : keyMomentRows (1417 : Fin 2886) =
    keyMomentRow1417 := by decide +kernel

theorem keyMomentRowsAt1418 : keyMomentRows (1418 : Fin 2886) =
    keyMomentRow1418 := by decide +kernel

theorem keyMomentRowsAt1419 : keyMomentRows (1419 : Fin 2886) =
    keyMomentRow1419 := by decide +kernel

theorem keyMomentRowsAt1420 : keyMomentRows (1420 : Fin 2886) =
    keyMomentRow1420 := by decide +kernel

theorem keyMomentRowsAt1421 : keyMomentRows (1421 : Fin 2886) =
    keyMomentRow1421 := by decide +kernel

theorem keyMomentRowsAt1422 : keyMomentRows (1422 : Fin 2886) =
    keyMomentRow1422 := by decide +kernel

theorem keyMomentRowsAt1423 : keyMomentRows (1423 : Fin 2886) =
    keyMomentRow1423 := by decide +kernel

theorem keyMomentRowsAt1424 : keyMomentRows (1424 : Fin 2886) =
    keyMomentRow1424 := by decide +kernel

theorem keyMomentRowsAt1425 : keyMomentRows (1425 : Fin 2886) =
    keyMomentRow1425 := by decide +kernel

theorem keyMomentRowsAt1426 : keyMomentRows (1426 : Fin 2886) =
    keyMomentRow1426 := by decide +kernel

theorem keyMomentRowsAt1427 : keyMomentRows (1427 : Fin 2886) =
    keyMomentRow1427 := by decide +kernel

theorem keyMomentRowsAt1428 : keyMomentRows (1428 : Fin 2886) =
    keyMomentRow1428 := by decide +kernel

theorem keyMomentRowsAt1429 : keyMomentRows (1429 : Fin 2886) =
    keyMomentRow1429 := by decide +kernel

theorem keyMomentRowsAt1430 : keyMomentRows (1430 : Fin 2886) =
    keyMomentRow1430 := by decide +kernel

theorem keyMomentRowsAt1431 : keyMomentRows (1431 : Fin 2886) =
    keyMomentRow1431 := by decide +kernel

theorem keyMomentRowsAt1432 : keyMomentRows (1432 : Fin 2886) =
    keyMomentRow1432 := by decide +kernel

theorem keyMomentRowsAt1433 : keyMomentRows (1433 : Fin 2886) =
    keyMomentRow1433 := by decide +kernel

theorem keyMomentRowsAt1434 : keyMomentRows (1434 : Fin 2886) =
    keyMomentRow1434 := by decide +kernel

theorem keyMomentRowsAt1435 : keyMomentRows (1435 : Fin 2886) =
    keyMomentRow1435 := by decide +kernel

theorem keyMomentRowsAt1436 : keyMomentRows (1436 : Fin 2886) =
    keyMomentRow1436 := by decide +kernel

theorem keyMomentRowsAt1437 : keyMomentRows (1437 : Fin 2886) =
    keyMomentRow1437 := by decide +kernel

theorem keyMomentRowsAt1438 : keyMomentRows (1438 : Fin 2886) =
    keyMomentRow1438 := by decide +kernel

theorem keyMomentRowsAt1439 : keyMomentRows (1439 : Fin 2886) =
    keyMomentRow1439 := by decide +kernel

theorem keyMomentChunkSound44 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 44) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1408 ∨ k.val = 1409 ∨ k.val = 1410 ∨ k.val = 1411 ∨ k.val = 1412 ∨ k.val = 1413 ∨ k.val = 1414 ∨ k.val = 1415 ∨ k.val = 1416 ∨ k.val = 1417 ∨ k.val = 1418 ∨ k.val = 1419 ∨ k.val = 1420 ∨ k.val = 1421 ∨ k.val = 1422 ∨ k.val = 1423 ∨ k.val = 1424 ∨ k.val = 1425 ∨ k.val = 1426 ∨ k.val = 1427 ∨ k.val = 1428 ∨ k.val = 1429 ∨ k.val = 1430 ∨ k.val = 1431 ∨ k.val = 1432 ∨ k.val = 1433 ∨ k.val = 1434 ∨ k.val = 1435 ∨ k.val = 1436 ∨ k.val = 1437 ∨ k.val = 1438 ∨ k.val = 1439 := by omega
  rcases heq with h1408 | h1409 | h1410 | h1411 | h1412 | h1413 | h1414 | h1415 | h1416 | h1417 | h1418 | h1419 | h1420 | h1421 | h1422 | h1423 | h1424 | h1425 | h1426 | h1427 | h1428 | h1429 | h1430 | h1431 | h1432 | h1433 | h1434 | h1435 | h1436 | h1437 | h1438 | h1439
  · have he : k = (1408 : Fin 2886) := Fin.ext h1408
    subst k
    rw [keyMomentRowsAt1408]
    exact keyMoment1408 B hB
  · have he : k = (1409 : Fin 2886) := Fin.ext h1409
    subst k
    rw [keyMomentRowsAt1409]
    exact keyMoment1409 B hB
  · have he : k = (1410 : Fin 2886) := Fin.ext h1410
    subst k
    rw [keyMomentRowsAt1410]
    exact keyMoment1410 B hB
  · have he : k = (1411 : Fin 2886) := Fin.ext h1411
    subst k
    rw [keyMomentRowsAt1411]
    exact keyMoment1411 B hB
  · have he : k = (1412 : Fin 2886) := Fin.ext h1412
    subst k
    rw [keyMomentRowsAt1412]
    exact keyMoment1412 B hB
  · have he : k = (1413 : Fin 2886) := Fin.ext h1413
    subst k
    rw [keyMomentRowsAt1413]
    exact keyMoment1413 B hB
  · have he : k = (1414 : Fin 2886) := Fin.ext h1414
    subst k
    rw [keyMomentRowsAt1414]
    exact keyMoment1414 B hB
  · have he : k = (1415 : Fin 2886) := Fin.ext h1415
    subst k
    rw [keyMomentRowsAt1415]
    exact keyMoment1415 B hB
  · have he : k = (1416 : Fin 2886) := Fin.ext h1416
    subst k
    rw [keyMomentRowsAt1416]
    exact keyMoment1416 B hB
  · have he : k = (1417 : Fin 2886) := Fin.ext h1417
    subst k
    rw [keyMomentRowsAt1417]
    exact keyMoment1417 B hB
  · have he : k = (1418 : Fin 2886) := Fin.ext h1418
    subst k
    rw [keyMomentRowsAt1418]
    exact keyMoment1418 B hB
  · have he : k = (1419 : Fin 2886) := Fin.ext h1419
    subst k
    rw [keyMomentRowsAt1419]
    exact keyMoment1419 B hB
  · have he : k = (1420 : Fin 2886) := Fin.ext h1420
    subst k
    rw [keyMomentRowsAt1420]
    exact keyMoment1420 B hB
  · have he : k = (1421 : Fin 2886) := Fin.ext h1421
    subst k
    rw [keyMomentRowsAt1421]
    exact keyMoment1421 B hB
  · have he : k = (1422 : Fin 2886) := Fin.ext h1422
    subst k
    rw [keyMomentRowsAt1422]
    exact keyMoment1422 B hB
  · have he : k = (1423 : Fin 2886) := Fin.ext h1423
    subst k
    rw [keyMomentRowsAt1423]
    exact keyMoment1423 B hB
  · have he : k = (1424 : Fin 2886) := Fin.ext h1424
    subst k
    rw [keyMomentRowsAt1424]
    exact keyMoment1424 B hB
  · have he : k = (1425 : Fin 2886) := Fin.ext h1425
    subst k
    rw [keyMomentRowsAt1425]
    exact keyMoment1425 B hB
  · have he : k = (1426 : Fin 2886) := Fin.ext h1426
    subst k
    rw [keyMomentRowsAt1426]
    exact keyMoment1426 B hB
  · have he : k = (1427 : Fin 2886) := Fin.ext h1427
    subst k
    rw [keyMomentRowsAt1427]
    exact keyMoment1427 B hB
  · have he : k = (1428 : Fin 2886) := Fin.ext h1428
    subst k
    rw [keyMomentRowsAt1428]
    exact keyMoment1428 B hB
  · have he : k = (1429 : Fin 2886) := Fin.ext h1429
    subst k
    rw [keyMomentRowsAt1429]
    exact keyMoment1429 B hB
  · have he : k = (1430 : Fin 2886) := Fin.ext h1430
    subst k
    rw [keyMomentRowsAt1430]
    exact keyMoment1430 B hB
  · have he : k = (1431 : Fin 2886) := Fin.ext h1431
    subst k
    rw [keyMomentRowsAt1431]
    exact keyMoment1431 B hB
  · have he : k = (1432 : Fin 2886) := Fin.ext h1432
    subst k
    rw [keyMomentRowsAt1432]
    exact keyMoment1432 B hB
  · have he : k = (1433 : Fin 2886) := Fin.ext h1433
    subst k
    rw [keyMomentRowsAt1433]
    exact keyMoment1433 B hB
  · have he : k = (1434 : Fin 2886) := Fin.ext h1434
    subst k
    rw [keyMomentRowsAt1434]
    exact keyMoment1434 B hB
  · have he : k = (1435 : Fin 2886) := Fin.ext h1435
    subst k
    rw [keyMomentRowsAt1435]
    exact keyMoment1435 B hB
  · have he : k = (1436 : Fin 2886) := Fin.ext h1436
    subst k
    rw [keyMomentRowsAt1436]
    exact keyMoment1436 B hB
  · have he : k = (1437 : Fin 2886) := Fin.ext h1437
    subst k
    rw [keyMomentRowsAt1437]
    exact keyMoment1437 B hB
  · have he : k = (1438 : Fin 2886) := Fin.ext h1438
    subst k
    rw [keyMomentRowsAt1438]
    exact keyMoment1438 B hB
  · have he : k = (1439 : Fin 2886) := Fin.ext h1439
    subst k
    rw [keyMomentRowsAt1439]
    exact keyMoment1439 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
