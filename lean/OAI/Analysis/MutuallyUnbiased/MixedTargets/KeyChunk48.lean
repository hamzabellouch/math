import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound48
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1536 : keyMomentRows (1536 : Fin 2886) =
    keyMomentRow1536 := by decide +kernel

theorem keyMomentRowsAt1537 : keyMomentRows (1537 : Fin 2886) =
    keyMomentRow1537 := by decide +kernel

theorem keyMomentRowsAt1538 : keyMomentRows (1538 : Fin 2886) =
    keyMomentRow1538 := by decide +kernel

theorem keyMomentRowsAt1539 : keyMomentRows (1539 : Fin 2886) =
    keyMomentRow1539 := by decide +kernel

theorem keyMomentRowsAt1540 : keyMomentRows (1540 : Fin 2886) =
    keyMomentRow1540 := by decide +kernel

theorem keyMomentRowsAt1541 : keyMomentRows (1541 : Fin 2886) =
    keyMomentRow1541 := by decide +kernel

theorem keyMomentRowsAt1542 : keyMomentRows (1542 : Fin 2886) =
    keyMomentRow1542 := by decide +kernel

theorem keyMomentRowsAt1543 : keyMomentRows (1543 : Fin 2886) =
    keyMomentRow1543 := by decide +kernel

theorem keyMomentRowsAt1544 : keyMomentRows (1544 : Fin 2886) =
    keyMomentRow1544 := by decide +kernel

theorem keyMomentRowsAt1545 : keyMomentRows (1545 : Fin 2886) =
    keyMomentRow1545 := by decide +kernel

theorem keyMomentRowsAt1546 : keyMomentRows (1546 : Fin 2886) =
    keyMomentRow1546 := by decide +kernel

theorem keyMomentRowsAt1547 : keyMomentRows (1547 : Fin 2886) =
    keyMomentRow1547 := by decide +kernel

theorem keyMomentRowsAt1548 : keyMomentRows (1548 : Fin 2886) =
    keyMomentRow1548 := by decide +kernel

theorem keyMomentRowsAt1549 : keyMomentRows (1549 : Fin 2886) =
    keyMomentRow1549 := by decide +kernel

theorem keyMomentRowsAt1550 : keyMomentRows (1550 : Fin 2886) =
    keyMomentRow1550 := by decide +kernel

theorem keyMomentRowsAt1551 : keyMomentRows (1551 : Fin 2886) =
    keyMomentRow1551 := by decide +kernel

theorem keyMomentRowsAt1552 : keyMomentRows (1552 : Fin 2886) =
    keyMomentRow1552 := by decide +kernel

theorem keyMomentRowsAt1553 : keyMomentRows (1553 : Fin 2886) =
    keyMomentRow1553 := by decide +kernel

theorem keyMomentRowsAt1554 : keyMomentRows (1554 : Fin 2886) =
    keyMomentRow1554 := by decide +kernel

theorem keyMomentRowsAt1555 : keyMomentRows (1555 : Fin 2886) =
    keyMomentRow1555 := by decide +kernel

theorem keyMomentRowsAt1556 : keyMomentRows (1556 : Fin 2886) =
    keyMomentRow1556 := by decide +kernel

theorem keyMomentRowsAt1557 : keyMomentRows (1557 : Fin 2886) =
    keyMomentRow1557 := by decide +kernel

theorem keyMomentRowsAt1558 : keyMomentRows (1558 : Fin 2886) =
    keyMomentRow1558 := by decide +kernel

theorem keyMomentRowsAt1559 : keyMomentRows (1559 : Fin 2886) =
    keyMomentRow1559 := by decide +kernel

theorem keyMomentRowsAt1560 : keyMomentRows (1560 : Fin 2886) =
    keyMomentRow1560 := by decide +kernel

theorem keyMomentRowsAt1561 : keyMomentRows (1561 : Fin 2886) =
    keyMomentRow1561 := by decide +kernel

theorem keyMomentRowsAt1562 : keyMomentRows (1562 : Fin 2886) =
    keyMomentRow1562 := by decide +kernel

theorem keyMomentRowsAt1563 : keyMomentRows (1563 : Fin 2886) =
    keyMomentRow1563 := by decide +kernel

theorem keyMomentRowsAt1564 : keyMomentRows (1564 : Fin 2886) =
    keyMomentRow1564 := by decide +kernel

theorem keyMomentRowsAt1565 : keyMomentRows (1565 : Fin 2886) =
    keyMomentRow1565 := by decide +kernel

theorem keyMomentRowsAt1566 : keyMomentRows (1566 : Fin 2886) =
    keyMomentRow1566 := by decide +kernel

theorem keyMomentRowsAt1567 : keyMomentRows (1567 : Fin 2886) =
    keyMomentRow1567 := by decide +kernel

theorem keyMomentChunkSound48 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 48) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1536 ∨ k.val = 1537 ∨ k.val = 1538 ∨ k.val = 1539 ∨ k.val = 1540 ∨ k.val = 1541 ∨ k.val = 1542 ∨ k.val = 1543 ∨ k.val = 1544 ∨ k.val = 1545 ∨ k.val = 1546 ∨ k.val = 1547 ∨ k.val = 1548 ∨ k.val = 1549 ∨ k.val = 1550 ∨ k.val = 1551 ∨ k.val = 1552 ∨ k.val = 1553 ∨ k.val = 1554 ∨ k.val = 1555 ∨ k.val = 1556 ∨ k.val = 1557 ∨ k.val = 1558 ∨ k.val = 1559 ∨ k.val = 1560 ∨ k.val = 1561 ∨ k.val = 1562 ∨ k.val = 1563 ∨ k.val = 1564 ∨ k.val = 1565 ∨ k.val = 1566 ∨ k.val = 1567 := by omega
  rcases heq with h1536 | h1537 | h1538 | h1539 | h1540 | h1541 | h1542 | h1543 | h1544 | h1545 | h1546 | h1547 | h1548 | h1549 | h1550 | h1551 | h1552 | h1553 | h1554 | h1555 | h1556 | h1557 | h1558 | h1559 | h1560 | h1561 | h1562 | h1563 | h1564 | h1565 | h1566 | h1567
  · have he : k = (1536 : Fin 2886) := Fin.ext h1536
    subst k
    rw [keyMomentRowsAt1536]
    exact keyMoment1536 B hB
  · have he : k = (1537 : Fin 2886) := Fin.ext h1537
    subst k
    rw [keyMomentRowsAt1537]
    exact keyMoment1537 B hB
  · have he : k = (1538 : Fin 2886) := Fin.ext h1538
    subst k
    rw [keyMomentRowsAt1538]
    exact keyMoment1538 B hB
  · have he : k = (1539 : Fin 2886) := Fin.ext h1539
    subst k
    rw [keyMomentRowsAt1539]
    exact keyMoment1539 B hB
  · have he : k = (1540 : Fin 2886) := Fin.ext h1540
    subst k
    rw [keyMomentRowsAt1540]
    exact keyMoment1540 B hB
  · have he : k = (1541 : Fin 2886) := Fin.ext h1541
    subst k
    rw [keyMomentRowsAt1541]
    exact keyMoment1541 B hB
  · have he : k = (1542 : Fin 2886) := Fin.ext h1542
    subst k
    rw [keyMomentRowsAt1542]
    exact keyMoment1542 B hB
  · have he : k = (1543 : Fin 2886) := Fin.ext h1543
    subst k
    rw [keyMomentRowsAt1543]
    exact keyMoment1543 B hB
  · have he : k = (1544 : Fin 2886) := Fin.ext h1544
    subst k
    rw [keyMomentRowsAt1544]
    exact keyMoment1544 B hB
  · have he : k = (1545 : Fin 2886) := Fin.ext h1545
    subst k
    rw [keyMomentRowsAt1545]
    exact keyMoment1545 B hB
  · have he : k = (1546 : Fin 2886) := Fin.ext h1546
    subst k
    rw [keyMomentRowsAt1546]
    exact keyMoment1546 B hB
  · have he : k = (1547 : Fin 2886) := Fin.ext h1547
    subst k
    rw [keyMomentRowsAt1547]
    exact keyMoment1547 B hB
  · have he : k = (1548 : Fin 2886) := Fin.ext h1548
    subst k
    rw [keyMomentRowsAt1548]
    exact keyMoment1548 B hB
  · have he : k = (1549 : Fin 2886) := Fin.ext h1549
    subst k
    rw [keyMomentRowsAt1549]
    exact keyMoment1549 B hB
  · have he : k = (1550 : Fin 2886) := Fin.ext h1550
    subst k
    rw [keyMomentRowsAt1550]
    exact keyMoment1550 B hB
  · have he : k = (1551 : Fin 2886) := Fin.ext h1551
    subst k
    rw [keyMomentRowsAt1551]
    exact keyMoment1551 B hB
  · have he : k = (1552 : Fin 2886) := Fin.ext h1552
    subst k
    rw [keyMomentRowsAt1552]
    exact keyMoment1552 B hB
  · have he : k = (1553 : Fin 2886) := Fin.ext h1553
    subst k
    rw [keyMomentRowsAt1553]
    exact keyMoment1553 B hB
  · have he : k = (1554 : Fin 2886) := Fin.ext h1554
    subst k
    rw [keyMomentRowsAt1554]
    exact keyMoment1554 B hB
  · have he : k = (1555 : Fin 2886) := Fin.ext h1555
    subst k
    rw [keyMomentRowsAt1555]
    exact keyMoment1555 B hB
  · have he : k = (1556 : Fin 2886) := Fin.ext h1556
    subst k
    rw [keyMomentRowsAt1556]
    exact keyMoment1556 B hB
  · have he : k = (1557 : Fin 2886) := Fin.ext h1557
    subst k
    rw [keyMomentRowsAt1557]
    exact keyMoment1557 B hB
  · have he : k = (1558 : Fin 2886) := Fin.ext h1558
    subst k
    rw [keyMomentRowsAt1558]
    exact keyMoment1558 B hB
  · have he : k = (1559 : Fin 2886) := Fin.ext h1559
    subst k
    rw [keyMomentRowsAt1559]
    exact keyMoment1559 B hB
  · have he : k = (1560 : Fin 2886) := Fin.ext h1560
    subst k
    rw [keyMomentRowsAt1560]
    exact keyMoment1560 B hB
  · have he : k = (1561 : Fin 2886) := Fin.ext h1561
    subst k
    rw [keyMomentRowsAt1561]
    exact keyMoment1561 B hB
  · have he : k = (1562 : Fin 2886) := Fin.ext h1562
    subst k
    rw [keyMomentRowsAt1562]
    exact keyMoment1562 B hB
  · have he : k = (1563 : Fin 2886) := Fin.ext h1563
    subst k
    rw [keyMomentRowsAt1563]
    exact keyMoment1563 B hB
  · have he : k = (1564 : Fin 2886) := Fin.ext h1564
    subst k
    rw [keyMomentRowsAt1564]
    exact keyMoment1564 B hB
  · have he : k = (1565 : Fin 2886) := Fin.ext h1565
    subst k
    rw [keyMomentRowsAt1565]
    exact keyMoment1565 B hB
  · have he : k = (1566 : Fin 2886) := Fin.ext h1566
    subst k
    rw [keyMomentRowsAt1566]
    exact keyMoment1566 B hB
  · have he : k = (1567 : Fin 2886) := Fin.ext h1567
    subst k
    rw [keyMomentRowsAt1567]
    exact keyMoment1567 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
