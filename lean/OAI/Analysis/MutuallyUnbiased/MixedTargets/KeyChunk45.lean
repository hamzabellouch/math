import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound45
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1440 : keyMomentRows (1440 : Fin 2886) =
    keyMomentRow1440 := by decide +kernel

theorem keyMomentRowsAt1441 : keyMomentRows (1441 : Fin 2886) =
    keyMomentRow1441 := by decide +kernel

theorem keyMomentRowsAt1442 : keyMomentRows (1442 : Fin 2886) =
    keyMomentRow1442 := by decide +kernel

theorem keyMomentRowsAt1443 : keyMomentRows (1443 : Fin 2886) =
    keyMomentRow1443 := by decide +kernel

theorem keyMomentRowsAt1444 : keyMomentRows (1444 : Fin 2886) =
    keyMomentRow1444 := by decide +kernel

theorem keyMomentRowsAt1445 : keyMomentRows (1445 : Fin 2886) =
    keyMomentRow1445 := by decide +kernel

theorem keyMomentRowsAt1446 : keyMomentRows (1446 : Fin 2886) =
    keyMomentRow1446 := by decide +kernel

theorem keyMomentRowsAt1447 : keyMomentRows (1447 : Fin 2886) =
    keyMomentRow1447 := by decide +kernel

theorem keyMomentRowsAt1448 : keyMomentRows (1448 : Fin 2886) =
    keyMomentRow1448 := by decide +kernel

theorem keyMomentRowsAt1449 : keyMomentRows (1449 : Fin 2886) =
    keyMomentRow1449 := by decide +kernel

theorem keyMomentRowsAt1450 : keyMomentRows (1450 : Fin 2886) =
    keyMomentRow1450 := by decide +kernel

theorem keyMomentRowsAt1451 : keyMomentRows (1451 : Fin 2886) =
    keyMomentRow1451 := by decide +kernel

theorem keyMomentRowsAt1452 : keyMomentRows (1452 : Fin 2886) =
    keyMomentRow1452 := by decide +kernel

theorem keyMomentRowsAt1453 : keyMomentRows (1453 : Fin 2886) =
    keyMomentRow1453 := by decide +kernel

theorem keyMomentRowsAt1454 : keyMomentRows (1454 : Fin 2886) =
    keyMomentRow1454 := by decide +kernel

theorem keyMomentRowsAt1455 : keyMomentRows (1455 : Fin 2886) =
    keyMomentRow1455 := by decide +kernel

theorem keyMomentRowsAt1456 : keyMomentRows (1456 : Fin 2886) =
    keyMomentRow1456 := by decide +kernel

theorem keyMomentRowsAt1457 : keyMomentRows (1457 : Fin 2886) =
    keyMomentRow1457 := by decide +kernel

theorem keyMomentRowsAt1458 : keyMomentRows (1458 : Fin 2886) =
    keyMomentRow1458 := by decide +kernel

theorem keyMomentRowsAt1459 : keyMomentRows (1459 : Fin 2886) =
    keyMomentRow1459 := by decide +kernel

theorem keyMomentRowsAt1460 : keyMomentRows (1460 : Fin 2886) =
    keyMomentRow1460 := by decide +kernel

theorem keyMomentRowsAt1461 : keyMomentRows (1461 : Fin 2886) =
    keyMomentRow1461 := by decide +kernel

theorem keyMomentRowsAt1462 : keyMomentRows (1462 : Fin 2886) =
    keyMomentRow1462 := by decide +kernel

theorem keyMomentRowsAt1463 : keyMomentRows (1463 : Fin 2886) =
    keyMomentRow1463 := by decide +kernel

theorem keyMomentRowsAt1464 : keyMomentRows (1464 : Fin 2886) =
    keyMomentRow1464 := by decide +kernel

theorem keyMomentRowsAt1465 : keyMomentRows (1465 : Fin 2886) =
    keyMomentRow1465 := by decide +kernel

theorem keyMomentRowsAt1466 : keyMomentRows (1466 : Fin 2886) =
    keyMomentRow1466 := by decide +kernel

theorem keyMomentRowsAt1467 : keyMomentRows (1467 : Fin 2886) =
    keyMomentRow1467 := by decide +kernel

theorem keyMomentRowsAt1468 : keyMomentRows (1468 : Fin 2886) =
    keyMomentRow1468 := by decide +kernel

theorem keyMomentRowsAt1469 : keyMomentRows (1469 : Fin 2886) =
    keyMomentRow1469 := by decide +kernel

theorem keyMomentRowsAt1470 : keyMomentRows (1470 : Fin 2886) =
    keyMomentRow1470 := by decide +kernel

theorem keyMomentRowsAt1471 : keyMomentRows (1471 : Fin 2886) =
    keyMomentRow1471 := by decide +kernel

theorem keyMomentChunkSound45 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 45) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1440 ∨ k.val = 1441 ∨ k.val = 1442 ∨ k.val = 1443 ∨ k.val = 1444 ∨ k.val = 1445 ∨ k.val = 1446 ∨ k.val = 1447 ∨ k.val = 1448 ∨ k.val = 1449 ∨ k.val = 1450 ∨ k.val = 1451 ∨ k.val = 1452 ∨ k.val = 1453 ∨ k.val = 1454 ∨ k.val = 1455 ∨ k.val = 1456 ∨ k.val = 1457 ∨ k.val = 1458 ∨ k.val = 1459 ∨ k.val = 1460 ∨ k.val = 1461 ∨ k.val = 1462 ∨ k.val = 1463 ∨ k.val = 1464 ∨ k.val = 1465 ∨ k.val = 1466 ∨ k.val = 1467 ∨ k.val = 1468 ∨ k.val = 1469 ∨ k.val = 1470 ∨ k.val = 1471 := by omega
  rcases heq with h1440 | h1441 | h1442 | h1443 | h1444 | h1445 | h1446 | h1447 | h1448 | h1449 | h1450 | h1451 | h1452 | h1453 | h1454 | h1455 | h1456 | h1457 | h1458 | h1459 | h1460 | h1461 | h1462 | h1463 | h1464 | h1465 | h1466 | h1467 | h1468 | h1469 | h1470 | h1471
  · have he : k = (1440 : Fin 2886) := Fin.ext h1440
    subst k
    rw [keyMomentRowsAt1440]
    exact keyMoment1440 B hB
  · have he : k = (1441 : Fin 2886) := Fin.ext h1441
    subst k
    rw [keyMomentRowsAt1441]
    exact keyMoment1441 B hB
  · have he : k = (1442 : Fin 2886) := Fin.ext h1442
    subst k
    rw [keyMomentRowsAt1442]
    exact keyMoment1442 B hB
  · have he : k = (1443 : Fin 2886) := Fin.ext h1443
    subst k
    rw [keyMomentRowsAt1443]
    exact keyMoment1443 B hB
  · have he : k = (1444 : Fin 2886) := Fin.ext h1444
    subst k
    rw [keyMomentRowsAt1444]
    exact keyMoment1444 B hB
  · have he : k = (1445 : Fin 2886) := Fin.ext h1445
    subst k
    rw [keyMomentRowsAt1445]
    exact keyMoment1445 B hB
  · have he : k = (1446 : Fin 2886) := Fin.ext h1446
    subst k
    rw [keyMomentRowsAt1446]
    exact keyMoment1446 B hB
  · have he : k = (1447 : Fin 2886) := Fin.ext h1447
    subst k
    rw [keyMomentRowsAt1447]
    exact keyMoment1447 B hB
  · have he : k = (1448 : Fin 2886) := Fin.ext h1448
    subst k
    rw [keyMomentRowsAt1448]
    exact keyMoment1448 B hB
  · have he : k = (1449 : Fin 2886) := Fin.ext h1449
    subst k
    rw [keyMomentRowsAt1449]
    exact keyMoment1449 B hB
  · have he : k = (1450 : Fin 2886) := Fin.ext h1450
    subst k
    rw [keyMomentRowsAt1450]
    exact keyMoment1450 B hB
  · have he : k = (1451 : Fin 2886) := Fin.ext h1451
    subst k
    rw [keyMomentRowsAt1451]
    exact keyMoment1451 B hB
  · have he : k = (1452 : Fin 2886) := Fin.ext h1452
    subst k
    rw [keyMomentRowsAt1452]
    exact keyMoment1452 B hB
  · have he : k = (1453 : Fin 2886) := Fin.ext h1453
    subst k
    rw [keyMomentRowsAt1453]
    exact keyMoment1453 B hB
  · have he : k = (1454 : Fin 2886) := Fin.ext h1454
    subst k
    rw [keyMomentRowsAt1454]
    exact keyMoment1454 B hB
  · have he : k = (1455 : Fin 2886) := Fin.ext h1455
    subst k
    rw [keyMomentRowsAt1455]
    exact keyMoment1455 B hB
  · have he : k = (1456 : Fin 2886) := Fin.ext h1456
    subst k
    rw [keyMomentRowsAt1456]
    exact keyMoment1456 B hB
  · have he : k = (1457 : Fin 2886) := Fin.ext h1457
    subst k
    rw [keyMomentRowsAt1457]
    exact keyMoment1457 B hB
  · have he : k = (1458 : Fin 2886) := Fin.ext h1458
    subst k
    rw [keyMomentRowsAt1458]
    exact keyMoment1458 B hB
  · have he : k = (1459 : Fin 2886) := Fin.ext h1459
    subst k
    rw [keyMomentRowsAt1459]
    exact keyMoment1459 B hB
  · have he : k = (1460 : Fin 2886) := Fin.ext h1460
    subst k
    rw [keyMomentRowsAt1460]
    exact keyMoment1460 B hB
  · have he : k = (1461 : Fin 2886) := Fin.ext h1461
    subst k
    rw [keyMomentRowsAt1461]
    exact keyMoment1461 B hB
  · have he : k = (1462 : Fin 2886) := Fin.ext h1462
    subst k
    rw [keyMomentRowsAt1462]
    exact keyMoment1462 B hB
  · have he : k = (1463 : Fin 2886) := Fin.ext h1463
    subst k
    rw [keyMomentRowsAt1463]
    exact keyMoment1463 B hB
  · have he : k = (1464 : Fin 2886) := Fin.ext h1464
    subst k
    rw [keyMomentRowsAt1464]
    exact keyMoment1464 B hB
  · have he : k = (1465 : Fin 2886) := Fin.ext h1465
    subst k
    rw [keyMomentRowsAt1465]
    exact keyMoment1465 B hB
  · have he : k = (1466 : Fin 2886) := Fin.ext h1466
    subst k
    rw [keyMomentRowsAt1466]
    exact keyMoment1466 B hB
  · have he : k = (1467 : Fin 2886) := Fin.ext h1467
    subst k
    rw [keyMomentRowsAt1467]
    exact keyMoment1467 B hB
  · have he : k = (1468 : Fin 2886) := Fin.ext h1468
    subst k
    rw [keyMomentRowsAt1468]
    exact keyMoment1468 B hB
  · have he : k = (1469 : Fin 2886) := Fin.ext h1469
    subst k
    rw [keyMomentRowsAt1469]
    exact keyMoment1469 B hB
  · have he : k = (1470 : Fin 2886) := Fin.ext h1470
    subst k
    rw [keyMomentRowsAt1470]
    exact keyMoment1470 B hB
  · have he : k = (1471 : Fin 2886) := Fin.ext h1471
    subst k
    rw [keyMomentRowsAt1471]
    exact keyMoment1471 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
