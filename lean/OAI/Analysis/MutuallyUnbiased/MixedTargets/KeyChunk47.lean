import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound47
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1504 : keyMomentRows (1504 : Fin 2886) =
    keyMomentRow1504 := by decide +kernel

theorem keyMomentRowsAt1505 : keyMomentRows (1505 : Fin 2886) =
    keyMomentRow1505 := by decide +kernel

theorem keyMomentRowsAt1506 : keyMomentRows (1506 : Fin 2886) =
    keyMomentRow1506 := by decide +kernel

theorem keyMomentRowsAt1507 : keyMomentRows (1507 : Fin 2886) =
    keyMomentRow1507 := by decide +kernel

theorem keyMomentRowsAt1508 : keyMomentRows (1508 : Fin 2886) =
    keyMomentRow1508 := by decide +kernel

theorem keyMomentRowsAt1509 : keyMomentRows (1509 : Fin 2886) =
    keyMomentRow1509 := by decide +kernel

theorem keyMomentRowsAt1510 : keyMomentRows (1510 : Fin 2886) =
    keyMomentRow1510 := by decide +kernel

theorem keyMomentRowsAt1511 : keyMomentRows (1511 : Fin 2886) =
    keyMomentRow1511 := by decide +kernel

theorem keyMomentRowsAt1512 : keyMomentRows (1512 : Fin 2886) =
    keyMomentRow1512 := by decide +kernel

theorem keyMomentRowsAt1513 : keyMomentRows (1513 : Fin 2886) =
    keyMomentRow1513 := by decide +kernel

theorem keyMomentRowsAt1514 : keyMomentRows (1514 : Fin 2886) =
    keyMomentRow1514 := by decide +kernel

theorem keyMomentRowsAt1515 : keyMomentRows (1515 : Fin 2886) =
    keyMomentRow1515 := by decide +kernel

theorem keyMomentRowsAt1516 : keyMomentRows (1516 : Fin 2886) =
    keyMomentRow1516 := by decide +kernel

theorem keyMomentRowsAt1517 : keyMomentRows (1517 : Fin 2886) =
    keyMomentRow1517 := by decide +kernel

theorem keyMomentRowsAt1518 : keyMomentRows (1518 : Fin 2886) =
    keyMomentRow1518 := by decide +kernel

theorem keyMomentRowsAt1519 : keyMomentRows (1519 : Fin 2886) =
    keyMomentRow1519 := by decide +kernel

theorem keyMomentRowsAt1520 : keyMomentRows (1520 : Fin 2886) =
    keyMomentRow1520 := by decide +kernel

theorem keyMomentRowsAt1521 : keyMomentRows (1521 : Fin 2886) =
    keyMomentRow1521 := by decide +kernel

theorem keyMomentRowsAt1522 : keyMomentRows (1522 : Fin 2886) =
    keyMomentRow1522 := by decide +kernel

theorem keyMomentRowsAt1523 : keyMomentRows (1523 : Fin 2886) =
    keyMomentRow1523 := by decide +kernel

theorem keyMomentRowsAt1524 : keyMomentRows (1524 : Fin 2886) =
    keyMomentRow1524 := by decide +kernel

theorem keyMomentRowsAt1525 : keyMomentRows (1525 : Fin 2886) =
    keyMomentRow1525 := by decide +kernel

theorem keyMomentRowsAt1526 : keyMomentRows (1526 : Fin 2886) =
    keyMomentRow1526 := by decide +kernel

theorem keyMomentRowsAt1527 : keyMomentRows (1527 : Fin 2886) =
    keyMomentRow1527 := by decide +kernel

theorem keyMomentRowsAt1528 : keyMomentRows (1528 : Fin 2886) =
    keyMomentRow1528 := by decide +kernel

theorem keyMomentRowsAt1529 : keyMomentRows (1529 : Fin 2886) =
    keyMomentRow1529 := by decide +kernel

theorem keyMomentRowsAt1530 : keyMomentRows (1530 : Fin 2886) =
    keyMomentRow1530 := by decide +kernel

theorem keyMomentRowsAt1531 : keyMomentRows (1531 : Fin 2886) =
    keyMomentRow1531 := by decide +kernel

theorem keyMomentRowsAt1532 : keyMomentRows (1532 : Fin 2886) =
    keyMomentRow1532 := by decide +kernel

theorem keyMomentRowsAt1533 : keyMomentRows (1533 : Fin 2886) =
    keyMomentRow1533 := by decide +kernel

theorem keyMomentRowsAt1534 : keyMomentRows (1534 : Fin 2886) =
    keyMomentRow1534 := by decide +kernel

theorem keyMomentRowsAt1535 : keyMomentRows (1535 : Fin 2886) =
    keyMomentRow1535 := by decide +kernel

theorem keyMomentChunkSound47 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 47) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1504 ∨ k.val = 1505 ∨ k.val = 1506 ∨ k.val = 1507 ∨ k.val = 1508 ∨ k.val = 1509 ∨ k.val = 1510 ∨ k.val = 1511 ∨ k.val = 1512 ∨ k.val = 1513 ∨ k.val = 1514 ∨ k.val = 1515 ∨ k.val = 1516 ∨ k.val = 1517 ∨ k.val = 1518 ∨ k.val = 1519 ∨ k.val = 1520 ∨ k.val = 1521 ∨ k.val = 1522 ∨ k.val = 1523 ∨ k.val = 1524 ∨ k.val = 1525 ∨ k.val = 1526 ∨ k.val = 1527 ∨ k.val = 1528 ∨ k.val = 1529 ∨ k.val = 1530 ∨ k.val = 1531 ∨ k.val = 1532 ∨ k.val = 1533 ∨ k.val = 1534 ∨ k.val = 1535 := by omega
  rcases heq with h1504 | h1505 | h1506 | h1507 | h1508 | h1509 | h1510 | h1511 | h1512 | h1513 | h1514 | h1515 | h1516 | h1517 | h1518 | h1519 | h1520 | h1521 | h1522 | h1523 | h1524 | h1525 | h1526 | h1527 | h1528 | h1529 | h1530 | h1531 | h1532 | h1533 | h1534 | h1535
  · have he : k = (1504 : Fin 2886) := Fin.ext h1504
    subst k
    rw [keyMomentRowsAt1504]
    exact keyMoment1504 B hB
  · have he : k = (1505 : Fin 2886) := Fin.ext h1505
    subst k
    rw [keyMomentRowsAt1505]
    exact keyMoment1505 B hB
  · have he : k = (1506 : Fin 2886) := Fin.ext h1506
    subst k
    rw [keyMomentRowsAt1506]
    exact keyMoment1506 B hB
  · have he : k = (1507 : Fin 2886) := Fin.ext h1507
    subst k
    rw [keyMomentRowsAt1507]
    exact keyMoment1507 B hB
  · have he : k = (1508 : Fin 2886) := Fin.ext h1508
    subst k
    rw [keyMomentRowsAt1508]
    exact keyMoment1508 B hB
  · have he : k = (1509 : Fin 2886) := Fin.ext h1509
    subst k
    rw [keyMomentRowsAt1509]
    exact keyMoment1509 B hB
  · have he : k = (1510 : Fin 2886) := Fin.ext h1510
    subst k
    rw [keyMomentRowsAt1510]
    exact keyMoment1510 B hB
  · have he : k = (1511 : Fin 2886) := Fin.ext h1511
    subst k
    rw [keyMomentRowsAt1511]
    exact keyMoment1511 B hB
  · have he : k = (1512 : Fin 2886) := Fin.ext h1512
    subst k
    rw [keyMomentRowsAt1512]
    exact keyMoment1512 B hB
  · have he : k = (1513 : Fin 2886) := Fin.ext h1513
    subst k
    rw [keyMomentRowsAt1513]
    exact keyMoment1513 B hB
  · have he : k = (1514 : Fin 2886) := Fin.ext h1514
    subst k
    rw [keyMomentRowsAt1514]
    exact keyMoment1514 B hB
  · have he : k = (1515 : Fin 2886) := Fin.ext h1515
    subst k
    rw [keyMomentRowsAt1515]
    exact keyMoment1515 B hB
  · have he : k = (1516 : Fin 2886) := Fin.ext h1516
    subst k
    rw [keyMomentRowsAt1516]
    exact keyMoment1516 B hB
  · have he : k = (1517 : Fin 2886) := Fin.ext h1517
    subst k
    rw [keyMomentRowsAt1517]
    exact keyMoment1517 B hB
  · have he : k = (1518 : Fin 2886) := Fin.ext h1518
    subst k
    rw [keyMomentRowsAt1518]
    exact keyMoment1518 B hB
  · have he : k = (1519 : Fin 2886) := Fin.ext h1519
    subst k
    rw [keyMomentRowsAt1519]
    exact keyMoment1519 B hB
  · have he : k = (1520 : Fin 2886) := Fin.ext h1520
    subst k
    rw [keyMomentRowsAt1520]
    exact keyMoment1520 B hB
  · have he : k = (1521 : Fin 2886) := Fin.ext h1521
    subst k
    rw [keyMomentRowsAt1521]
    exact keyMoment1521 B hB
  · have he : k = (1522 : Fin 2886) := Fin.ext h1522
    subst k
    rw [keyMomentRowsAt1522]
    exact keyMoment1522 B hB
  · have he : k = (1523 : Fin 2886) := Fin.ext h1523
    subst k
    rw [keyMomentRowsAt1523]
    exact keyMoment1523 B hB
  · have he : k = (1524 : Fin 2886) := Fin.ext h1524
    subst k
    rw [keyMomentRowsAt1524]
    exact keyMoment1524 B hB
  · have he : k = (1525 : Fin 2886) := Fin.ext h1525
    subst k
    rw [keyMomentRowsAt1525]
    exact keyMoment1525 B hB
  · have he : k = (1526 : Fin 2886) := Fin.ext h1526
    subst k
    rw [keyMomentRowsAt1526]
    exact keyMoment1526 B hB
  · have he : k = (1527 : Fin 2886) := Fin.ext h1527
    subst k
    rw [keyMomentRowsAt1527]
    exact keyMoment1527 B hB
  · have he : k = (1528 : Fin 2886) := Fin.ext h1528
    subst k
    rw [keyMomentRowsAt1528]
    exact keyMoment1528 B hB
  · have he : k = (1529 : Fin 2886) := Fin.ext h1529
    subst k
    rw [keyMomentRowsAt1529]
    exact keyMoment1529 B hB
  · have he : k = (1530 : Fin 2886) := Fin.ext h1530
    subst k
    rw [keyMomentRowsAt1530]
    exact keyMoment1530 B hB
  · have he : k = (1531 : Fin 2886) := Fin.ext h1531
    subst k
    rw [keyMomentRowsAt1531]
    exact keyMoment1531 B hB
  · have he : k = (1532 : Fin 2886) := Fin.ext h1532
    subst k
    rw [keyMomentRowsAt1532]
    exact keyMoment1532 B hB
  · have he : k = (1533 : Fin 2886) := Fin.ext h1533
    subst k
    rw [keyMomentRowsAt1533]
    exact keyMoment1533 B hB
  · have he : k = (1534 : Fin 2886) := Fin.ext h1534
    subst k
    rw [keyMomentRowsAt1534]
    exact keyMoment1534 B hB
  · have he : k = (1535 : Fin 2886) := Fin.ext h1535
    subst k
    rw [keyMomentRowsAt1535]
    exact keyMoment1535 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
