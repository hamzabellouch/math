import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound50
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1600 : keyMomentRows (1600 : Fin 2886) =
    keyMomentRow1600 := by decide +kernel

theorem keyMomentRowsAt1601 : keyMomentRows (1601 : Fin 2886) =
    keyMomentRow1601 := by decide +kernel

theorem keyMomentRowsAt1602 : keyMomentRows (1602 : Fin 2886) =
    keyMomentRow1602 := by decide +kernel

theorem keyMomentRowsAt1603 : keyMomentRows (1603 : Fin 2886) =
    keyMomentRow1603 := by decide +kernel

theorem keyMomentRowsAt1604 : keyMomentRows (1604 : Fin 2886) =
    keyMomentRow1604 := by decide +kernel

theorem keyMomentRowsAt1605 : keyMomentRows (1605 : Fin 2886) =
    keyMomentRow1605 := by decide +kernel

theorem keyMomentRowsAt1606 : keyMomentRows (1606 : Fin 2886) =
    keyMomentRow1606 := by decide +kernel

theorem keyMomentRowsAt1607 : keyMomentRows (1607 : Fin 2886) =
    keyMomentRow1607 := by decide +kernel

theorem keyMomentRowsAt1608 : keyMomentRows (1608 : Fin 2886) =
    keyMomentRow1608 := by decide +kernel

theorem keyMomentRowsAt1609 : keyMomentRows (1609 : Fin 2886) =
    keyMomentRow1609 := by decide +kernel

theorem keyMomentRowsAt1610 : keyMomentRows (1610 : Fin 2886) =
    keyMomentRow1610 := by decide +kernel

theorem keyMomentRowsAt1611 : keyMomentRows (1611 : Fin 2886) =
    keyMomentRow1611 := by decide +kernel

theorem keyMomentRowsAt1612 : keyMomentRows (1612 : Fin 2886) =
    keyMomentRow1612 := by decide +kernel

theorem keyMomentRowsAt1613 : keyMomentRows (1613 : Fin 2886) =
    keyMomentRow1613 := by decide +kernel

theorem keyMomentRowsAt1614 : keyMomentRows (1614 : Fin 2886) =
    keyMomentRow1614 := by decide +kernel

theorem keyMomentRowsAt1615 : keyMomentRows (1615 : Fin 2886) =
    keyMomentRow1615 := by decide +kernel

theorem keyMomentRowsAt1616 : keyMomentRows (1616 : Fin 2886) =
    keyMomentRow1616 := by decide +kernel

theorem keyMomentRowsAt1617 : keyMomentRows (1617 : Fin 2886) =
    keyMomentRow1617 := by decide +kernel

theorem keyMomentRowsAt1618 : keyMomentRows (1618 : Fin 2886) =
    keyMomentRow1618 := by decide +kernel

theorem keyMomentRowsAt1619 : keyMomentRows (1619 : Fin 2886) =
    keyMomentRow1619 := by decide +kernel

theorem keyMomentRowsAt1620 : keyMomentRows (1620 : Fin 2886) =
    keyMomentRow1620 := by decide +kernel

theorem keyMomentRowsAt1621 : keyMomentRows (1621 : Fin 2886) =
    keyMomentRow1621 := by decide +kernel

theorem keyMomentRowsAt1622 : keyMomentRows (1622 : Fin 2886) =
    keyMomentRow1622 := by decide +kernel

theorem keyMomentRowsAt1623 : keyMomentRows (1623 : Fin 2886) =
    keyMomentRow1623 := by decide +kernel

theorem keyMomentRowsAt1624 : keyMomentRows (1624 : Fin 2886) =
    keyMomentRow1624 := by decide +kernel

theorem keyMomentRowsAt1625 : keyMomentRows (1625 : Fin 2886) =
    keyMomentRow1625 := by decide +kernel

theorem keyMomentRowsAt1626 : keyMomentRows (1626 : Fin 2886) =
    keyMomentRow1626 := by decide +kernel

theorem keyMomentRowsAt1627 : keyMomentRows (1627 : Fin 2886) =
    keyMomentRow1627 := by decide +kernel

theorem keyMomentRowsAt1628 : keyMomentRows (1628 : Fin 2886) =
    keyMomentRow1628 := by decide +kernel

theorem keyMomentRowsAt1629 : keyMomentRows (1629 : Fin 2886) =
    keyMomentRow1629 := by decide +kernel

theorem keyMomentRowsAt1630 : keyMomentRows (1630 : Fin 2886) =
    keyMomentRow1630 := by decide +kernel

theorem keyMomentRowsAt1631 : keyMomentRows (1631 : Fin 2886) =
    keyMomentRow1631 := by decide +kernel

theorem keyMomentChunkSound50 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 50) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1600 ∨ k.val = 1601 ∨ k.val = 1602 ∨ k.val = 1603 ∨ k.val = 1604 ∨ k.val = 1605 ∨ k.val = 1606 ∨ k.val = 1607 ∨ k.val = 1608 ∨ k.val = 1609 ∨ k.val = 1610 ∨ k.val = 1611 ∨ k.val = 1612 ∨ k.val = 1613 ∨ k.val = 1614 ∨ k.val = 1615 ∨ k.val = 1616 ∨ k.val = 1617 ∨ k.val = 1618 ∨ k.val = 1619 ∨ k.val = 1620 ∨ k.val = 1621 ∨ k.val = 1622 ∨ k.val = 1623 ∨ k.val = 1624 ∨ k.val = 1625 ∨ k.val = 1626 ∨ k.val = 1627 ∨ k.val = 1628 ∨ k.val = 1629 ∨ k.val = 1630 ∨ k.val = 1631 := by omega
  rcases heq with h1600 | h1601 | h1602 | h1603 | h1604 | h1605 | h1606 | h1607 | h1608 | h1609 | h1610 | h1611 | h1612 | h1613 | h1614 | h1615 | h1616 | h1617 | h1618 | h1619 | h1620 | h1621 | h1622 | h1623 | h1624 | h1625 | h1626 | h1627 | h1628 | h1629 | h1630 | h1631
  · have he : k = (1600 : Fin 2886) := Fin.ext h1600
    subst k
    rw [keyMomentRowsAt1600]
    exact keyMoment1600 B hB
  · have he : k = (1601 : Fin 2886) := Fin.ext h1601
    subst k
    rw [keyMomentRowsAt1601]
    exact keyMoment1601 B hB
  · have he : k = (1602 : Fin 2886) := Fin.ext h1602
    subst k
    rw [keyMomentRowsAt1602]
    exact keyMoment1602 B hB
  · have he : k = (1603 : Fin 2886) := Fin.ext h1603
    subst k
    rw [keyMomentRowsAt1603]
    exact keyMoment1603 B hB
  · have he : k = (1604 : Fin 2886) := Fin.ext h1604
    subst k
    rw [keyMomentRowsAt1604]
    exact keyMoment1604 B hB
  · have he : k = (1605 : Fin 2886) := Fin.ext h1605
    subst k
    rw [keyMomentRowsAt1605]
    exact keyMoment1605 B hB
  · have he : k = (1606 : Fin 2886) := Fin.ext h1606
    subst k
    rw [keyMomentRowsAt1606]
    exact keyMoment1606 B hB
  · have he : k = (1607 : Fin 2886) := Fin.ext h1607
    subst k
    rw [keyMomentRowsAt1607]
    exact keyMoment1607 B hB
  · have he : k = (1608 : Fin 2886) := Fin.ext h1608
    subst k
    rw [keyMomentRowsAt1608]
    exact keyMoment1608 B hB
  · have he : k = (1609 : Fin 2886) := Fin.ext h1609
    subst k
    rw [keyMomentRowsAt1609]
    exact keyMoment1609 B hB
  · have he : k = (1610 : Fin 2886) := Fin.ext h1610
    subst k
    rw [keyMomentRowsAt1610]
    exact keyMoment1610 B hB
  · have he : k = (1611 : Fin 2886) := Fin.ext h1611
    subst k
    rw [keyMomentRowsAt1611]
    exact keyMoment1611 B hB
  · have he : k = (1612 : Fin 2886) := Fin.ext h1612
    subst k
    rw [keyMomentRowsAt1612]
    exact keyMoment1612 B hB
  · have he : k = (1613 : Fin 2886) := Fin.ext h1613
    subst k
    rw [keyMomentRowsAt1613]
    exact keyMoment1613 B hB
  · have he : k = (1614 : Fin 2886) := Fin.ext h1614
    subst k
    rw [keyMomentRowsAt1614]
    exact keyMoment1614 B hB
  · have he : k = (1615 : Fin 2886) := Fin.ext h1615
    subst k
    rw [keyMomentRowsAt1615]
    exact keyMoment1615 B hB
  · have he : k = (1616 : Fin 2886) := Fin.ext h1616
    subst k
    rw [keyMomentRowsAt1616]
    exact keyMoment1616 B hB
  · have he : k = (1617 : Fin 2886) := Fin.ext h1617
    subst k
    rw [keyMomentRowsAt1617]
    exact keyMoment1617 B hB
  · have he : k = (1618 : Fin 2886) := Fin.ext h1618
    subst k
    rw [keyMomentRowsAt1618]
    exact keyMoment1618 B hB
  · have he : k = (1619 : Fin 2886) := Fin.ext h1619
    subst k
    rw [keyMomentRowsAt1619]
    exact keyMoment1619 B hB
  · have he : k = (1620 : Fin 2886) := Fin.ext h1620
    subst k
    rw [keyMomentRowsAt1620]
    exact keyMoment1620 B hB
  · have he : k = (1621 : Fin 2886) := Fin.ext h1621
    subst k
    rw [keyMomentRowsAt1621]
    exact keyMoment1621 B hB
  · have he : k = (1622 : Fin 2886) := Fin.ext h1622
    subst k
    rw [keyMomentRowsAt1622]
    exact keyMoment1622 B hB
  · have he : k = (1623 : Fin 2886) := Fin.ext h1623
    subst k
    rw [keyMomentRowsAt1623]
    exact keyMoment1623 B hB
  · have he : k = (1624 : Fin 2886) := Fin.ext h1624
    subst k
    rw [keyMomentRowsAt1624]
    exact keyMoment1624 B hB
  · have he : k = (1625 : Fin 2886) := Fin.ext h1625
    subst k
    rw [keyMomentRowsAt1625]
    exact keyMoment1625 B hB
  · have he : k = (1626 : Fin 2886) := Fin.ext h1626
    subst k
    rw [keyMomentRowsAt1626]
    exact keyMoment1626 B hB
  · have he : k = (1627 : Fin 2886) := Fin.ext h1627
    subst k
    rw [keyMomentRowsAt1627]
    exact keyMoment1627 B hB
  · have he : k = (1628 : Fin 2886) := Fin.ext h1628
    subst k
    rw [keyMomentRowsAt1628]
    exact keyMoment1628 B hB
  · have he : k = (1629 : Fin 2886) := Fin.ext h1629
    subst k
    rw [keyMomentRowsAt1629]
    exact keyMoment1629 B hB
  · have he : k = (1630 : Fin 2886) := Fin.ext h1630
    subst k
    rw [keyMomentRowsAt1630]
    exact keyMoment1630 B hB
  · have he : k = (1631 : Fin 2886) := Fin.ext h1631
    subst k
    rw [keyMomentRowsAt1631]
    exact keyMoment1631 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
