import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound49
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1568 : keyMomentRows (1568 : Fin 2886) =
    keyMomentRow1568 := by decide +kernel

theorem keyMomentRowsAt1569 : keyMomentRows (1569 : Fin 2886) =
    keyMomentRow1569 := by decide +kernel

theorem keyMomentRowsAt1570 : keyMomentRows (1570 : Fin 2886) =
    keyMomentRow1570 := by decide +kernel

theorem keyMomentRowsAt1571 : keyMomentRows (1571 : Fin 2886) =
    keyMomentRow1571 := by decide +kernel

theorem keyMomentRowsAt1572 : keyMomentRows (1572 : Fin 2886) =
    keyMomentRow1572 := by decide +kernel

theorem keyMomentRowsAt1573 : keyMomentRows (1573 : Fin 2886) =
    keyMomentRow1573 := by decide +kernel

theorem keyMomentRowsAt1574 : keyMomentRows (1574 : Fin 2886) =
    keyMomentRow1574 := by decide +kernel

theorem keyMomentRowsAt1575 : keyMomentRows (1575 : Fin 2886) =
    keyMomentRow1575 := by decide +kernel

theorem keyMomentRowsAt1576 : keyMomentRows (1576 : Fin 2886) =
    keyMomentRow1576 := by decide +kernel

theorem keyMomentRowsAt1577 : keyMomentRows (1577 : Fin 2886) =
    keyMomentRow1577 := by decide +kernel

theorem keyMomentRowsAt1578 : keyMomentRows (1578 : Fin 2886) =
    keyMomentRow1578 := by decide +kernel

theorem keyMomentRowsAt1579 : keyMomentRows (1579 : Fin 2886) =
    keyMomentRow1579 := by decide +kernel

theorem keyMomentRowsAt1580 : keyMomentRows (1580 : Fin 2886) =
    keyMomentRow1580 := by decide +kernel

theorem keyMomentRowsAt1581 : keyMomentRows (1581 : Fin 2886) =
    keyMomentRow1581 := by decide +kernel

theorem keyMomentRowsAt1582 : keyMomentRows (1582 : Fin 2886) =
    keyMomentRow1582 := by decide +kernel

theorem keyMomentRowsAt1583 : keyMomentRows (1583 : Fin 2886) =
    keyMomentRow1583 := by decide +kernel

theorem keyMomentRowsAt1584 : keyMomentRows (1584 : Fin 2886) =
    keyMomentRow1584 := by decide +kernel

theorem keyMomentRowsAt1585 : keyMomentRows (1585 : Fin 2886) =
    keyMomentRow1585 := by decide +kernel

theorem keyMomentRowsAt1586 : keyMomentRows (1586 : Fin 2886) =
    keyMomentRow1586 := by decide +kernel

theorem keyMomentRowsAt1587 : keyMomentRows (1587 : Fin 2886) =
    keyMomentRow1587 := by decide +kernel

theorem keyMomentRowsAt1588 : keyMomentRows (1588 : Fin 2886) =
    keyMomentRow1588 := by decide +kernel

theorem keyMomentRowsAt1589 : keyMomentRows (1589 : Fin 2886) =
    keyMomentRow1589 := by decide +kernel

theorem keyMomentRowsAt1590 : keyMomentRows (1590 : Fin 2886) =
    keyMomentRow1590 := by decide +kernel

theorem keyMomentRowsAt1591 : keyMomentRows (1591 : Fin 2886) =
    keyMomentRow1591 := by decide +kernel

theorem keyMomentRowsAt1592 : keyMomentRows (1592 : Fin 2886) =
    keyMomentRow1592 := by decide +kernel

theorem keyMomentRowsAt1593 : keyMomentRows (1593 : Fin 2886) =
    keyMomentRow1593 := by decide +kernel

theorem keyMomentRowsAt1594 : keyMomentRows (1594 : Fin 2886) =
    keyMomentRow1594 := by decide +kernel

theorem keyMomentRowsAt1595 : keyMomentRows (1595 : Fin 2886) =
    keyMomentRow1595 := by decide +kernel

theorem keyMomentRowsAt1596 : keyMomentRows (1596 : Fin 2886) =
    keyMomentRow1596 := by decide +kernel

theorem keyMomentRowsAt1597 : keyMomentRows (1597 : Fin 2886) =
    keyMomentRow1597 := by decide +kernel

theorem keyMomentRowsAt1598 : keyMomentRows (1598 : Fin 2886) =
    keyMomentRow1598 := by decide +kernel

theorem keyMomentRowsAt1599 : keyMomentRows (1599 : Fin 2886) =
    keyMomentRow1599 := by decide +kernel

theorem keyMomentChunkSound49 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 49) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1568 ∨ k.val = 1569 ∨ k.val = 1570 ∨ k.val = 1571 ∨ k.val = 1572 ∨ k.val = 1573 ∨ k.val = 1574 ∨ k.val = 1575 ∨ k.val = 1576 ∨ k.val = 1577 ∨ k.val = 1578 ∨ k.val = 1579 ∨ k.val = 1580 ∨ k.val = 1581 ∨ k.val = 1582 ∨ k.val = 1583 ∨ k.val = 1584 ∨ k.val = 1585 ∨ k.val = 1586 ∨ k.val = 1587 ∨ k.val = 1588 ∨ k.val = 1589 ∨ k.val = 1590 ∨ k.val = 1591 ∨ k.val = 1592 ∨ k.val = 1593 ∨ k.val = 1594 ∨ k.val = 1595 ∨ k.val = 1596 ∨ k.val = 1597 ∨ k.val = 1598 ∨ k.val = 1599 := by omega
  rcases heq with h1568 | h1569 | h1570 | h1571 | h1572 | h1573 | h1574 | h1575 | h1576 | h1577 | h1578 | h1579 | h1580 | h1581 | h1582 | h1583 | h1584 | h1585 | h1586 | h1587 | h1588 | h1589 | h1590 | h1591 | h1592 | h1593 | h1594 | h1595 | h1596 | h1597 | h1598 | h1599
  · have he : k = (1568 : Fin 2886) := Fin.ext h1568
    subst k
    rw [keyMomentRowsAt1568]
    exact keyMoment1568 B hB
  · have he : k = (1569 : Fin 2886) := Fin.ext h1569
    subst k
    rw [keyMomentRowsAt1569]
    exact keyMoment1569 B hB
  · have he : k = (1570 : Fin 2886) := Fin.ext h1570
    subst k
    rw [keyMomentRowsAt1570]
    exact keyMoment1570 B hB
  · have he : k = (1571 : Fin 2886) := Fin.ext h1571
    subst k
    rw [keyMomentRowsAt1571]
    exact keyMoment1571 B hB
  · have he : k = (1572 : Fin 2886) := Fin.ext h1572
    subst k
    rw [keyMomentRowsAt1572]
    exact keyMoment1572 B hB
  · have he : k = (1573 : Fin 2886) := Fin.ext h1573
    subst k
    rw [keyMomentRowsAt1573]
    exact keyMoment1573 B hB
  · have he : k = (1574 : Fin 2886) := Fin.ext h1574
    subst k
    rw [keyMomentRowsAt1574]
    exact keyMoment1574 B hB
  · have he : k = (1575 : Fin 2886) := Fin.ext h1575
    subst k
    rw [keyMomentRowsAt1575]
    exact keyMoment1575 B hB
  · have he : k = (1576 : Fin 2886) := Fin.ext h1576
    subst k
    rw [keyMomentRowsAt1576]
    exact keyMoment1576 B hB
  · have he : k = (1577 : Fin 2886) := Fin.ext h1577
    subst k
    rw [keyMomentRowsAt1577]
    exact keyMoment1577 B hB
  · have he : k = (1578 : Fin 2886) := Fin.ext h1578
    subst k
    rw [keyMomentRowsAt1578]
    exact keyMoment1578 B hB
  · have he : k = (1579 : Fin 2886) := Fin.ext h1579
    subst k
    rw [keyMomentRowsAt1579]
    exact keyMoment1579 B hB
  · have he : k = (1580 : Fin 2886) := Fin.ext h1580
    subst k
    rw [keyMomentRowsAt1580]
    exact keyMoment1580 B hB
  · have he : k = (1581 : Fin 2886) := Fin.ext h1581
    subst k
    rw [keyMomentRowsAt1581]
    exact keyMoment1581 B hB
  · have he : k = (1582 : Fin 2886) := Fin.ext h1582
    subst k
    rw [keyMomentRowsAt1582]
    exact keyMoment1582 B hB
  · have he : k = (1583 : Fin 2886) := Fin.ext h1583
    subst k
    rw [keyMomentRowsAt1583]
    exact keyMoment1583 B hB
  · have he : k = (1584 : Fin 2886) := Fin.ext h1584
    subst k
    rw [keyMomentRowsAt1584]
    exact keyMoment1584 B hB
  · have he : k = (1585 : Fin 2886) := Fin.ext h1585
    subst k
    rw [keyMomentRowsAt1585]
    exact keyMoment1585 B hB
  · have he : k = (1586 : Fin 2886) := Fin.ext h1586
    subst k
    rw [keyMomentRowsAt1586]
    exact keyMoment1586 B hB
  · have he : k = (1587 : Fin 2886) := Fin.ext h1587
    subst k
    rw [keyMomentRowsAt1587]
    exact keyMoment1587 B hB
  · have he : k = (1588 : Fin 2886) := Fin.ext h1588
    subst k
    rw [keyMomentRowsAt1588]
    exact keyMoment1588 B hB
  · have he : k = (1589 : Fin 2886) := Fin.ext h1589
    subst k
    rw [keyMomentRowsAt1589]
    exact keyMoment1589 B hB
  · have he : k = (1590 : Fin 2886) := Fin.ext h1590
    subst k
    rw [keyMomentRowsAt1590]
    exact keyMoment1590 B hB
  · have he : k = (1591 : Fin 2886) := Fin.ext h1591
    subst k
    rw [keyMomentRowsAt1591]
    exact keyMoment1591 B hB
  · have he : k = (1592 : Fin 2886) := Fin.ext h1592
    subst k
    rw [keyMomentRowsAt1592]
    exact keyMoment1592 B hB
  · have he : k = (1593 : Fin 2886) := Fin.ext h1593
    subst k
    rw [keyMomentRowsAt1593]
    exact keyMoment1593 B hB
  · have he : k = (1594 : Fin 2886) := Fin.ext h1594
    subst k
    rw [keyMomentRowsAt1594]
    exact keyMoment1594 B hB
  · have he : k = (1595 : Fin 2886) := Fin.ext h1595
    subst k
    rw [keyMomentRowsAt1595]
    exact keyMoment1595 B hB
  · have he : k = (1596 : Fin 2886) := Fin.ext h1596
    subst k
    rw [keyMomentRowsAt1596]
    exact keyMoment1596 B hB
  · have he : k = (1597 : Fin 2886) := Fin.ext h1597
    subst k
    rw [keyMomentRowsAt1597]
    exact keyMoment1597 B hB
  · have he : k = (1598 : Fin 2886) := Fin.ext h1598
    subst k
    rw [keyMomentRowsAt1598]
    exact keyMoment1598 B hB
  · have he : k = (1599 : Fin 2886) := Fin.ext h1599
    subst k
    rw [keyMomentRowsAt1599]
    exact keyMoment1599 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
