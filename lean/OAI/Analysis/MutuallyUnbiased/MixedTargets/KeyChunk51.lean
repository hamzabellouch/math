import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound51
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1632 : keyMomentRows (1632 : Fin 2886) =
    keyMomentRow1632 := by decide +kernel

theorem keyMomentRowsAt1633 : keyMomentRows (1633 : Fin 2886) =
    keyMomentRow1633 := by decide +kernel

theorem keyMomentRowsAt1634 : keyMomentRows (1634 : Fin 2886) =
    keyMomentRow1634 := by decide +kernel

theorem keyMomentRowsAt1635 : keyMomentRows (1635 : Fin 2886) =
    keyMomentRow1635 := by decide +kernel

theorem keyMomentRowsAt1636 : keyMomentRows (1636 : Fin 2886) =
    keyMomentRow1636 := by decide +kernel

theorem keyMomentRowsAt1637 : keyMomentRows (1637 : Fin 2886) =
    keyMomentRow1637 := by decide +kernel

theorem keyMomentRowsAt1638 : keyMomentRows (1638 : Fin 2886) =
    keyMomentRow1638 := by decide +kernel

theorem keyMomentRowsAt1639 : keyMomentRows (1639 : Fin 2886) =
    keyMomentRow1639 := by decide +kernel

theorem keyMomentRowsAt1640 : keyMomentRows (1640 : Fin 2886) =
    keyMomentRow1640 := by decide +kernel

theorem keyMomentRowsAt1641 : keyMomentRows (1641 : Fin 2886) =
    keyMomentRow1641 := by decide +kernel

theorem keyMomentRowsAt1642 : keyMomentRows (1642 : Fin 2886) =
    keyMomentRow1642 := by decide +kernel

theorem keyMomentRowsAt1643 : keyMomentRows (1643 : Fin 2886) =
    keyMomentRow1643 := by decide +kernel

theorem keyMomentRowsAt1644 : keyMomentRows (1644 : Fin 2886) =
    keyMomentRow1644 := by decide +kernel

theorem keyMomentRowsAt1645 : keyMomentRows (1645 : Fin 2886) =
    keyMomentRow1645 := by decide +kernel

theorem keyMomentRowsAt1646 : keyMomentRows (1646 : Fin 2886) =
    keyMomentRow1646 := by decide +kernel

theorem keyMomentRowsAt1647 : keyMomentRows (1647 : Fin 2886) =
    keyMomentRow1647 := by decide +kernel

theorem keyMomentRowsAt1648 : keyMomentRows (1648 : Fin 2886) =
    keyMomentRow1648 := by decide +kernel

theorem keyMomentRowsAt1649 : keyMomentRows (1649 : Fin 2886) =
    keyMomentRow1649 := by decide +kernel

theorem keyMomentRowsAt1650 : keyMomentRows (1650 : Fin 2886) =
    keyMomentRow1650 := by decide +kernel

theorem keyMomentRowsAt1651 : keyMomentRows (1651 : Fin 2886) =
    keyMomentRow1651 := by decide +kernel

theorem keyMomentRowsAt1652 : keyMomentRows (1652 : Fin 2886) =
    keyMomentRow1652 := by decide +kernel

theorem keyMomentRowsAt1653 : keyMomentRows (1653 : Fin 2886) =
    keyMomentRow1653 := by decide +kernel

theorem keyMomentRowsAt1654 : keyMomentRows (1654 : Fin 2886) =
    keyMomentRow1654 := by decide +kernel

theorem keyMomentRowsAt1655 : keyMomentRows (1655 : Fin 2886) =
    keyMomentRow1655 := by decide +kernel

theorem keyMomentRowsAt1656 : keyMomentRows (1656 : Fin 2886) =
    keyMomentRow1656 := by decide +kernel

theorem keyMomentRowsAt1657 : keyMomentRows (1657 : Fin 2886) =
    keyMomentRow1657 := by decide +kernel

theorem keyMomentRowsAt1658 : keyMomentRows (1658 : Fin 2886) =
    keyMomentRow1658 := by decide +kernel

theorem keyMomentRowsAt1659 : keyMomentRows (1659 : Fin 2886) =
    keyMomentRow1659 := by decide +kernel

theorem keyMomentRowsAt1660 : keyMomentRows (1660 : Fin 2886) =
    keyMomentRow1660 := by decide +kernel

theorem keyMomentRowsAt1661 : keyMomentRows (1661 : Fin 2886) =
    keyMomentRow1661 := by decide +kernel

theorem keyMomentRowsAt1662 : keyMomentRows (1662 : Fin 2886) =
    keyMomentRow1662 := by decide +kernel

theorem keyMomentRowsAt1663 : keyMomentRows (1663 : Fin 2886) =
    keyMomentRow1663 := by decide +kernel

theorem keyMomentChunkSound51 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 51) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1632 ∨ k.val = 1633 ∨ k.val = 1634 ∨ k.val = 1635 ∨ k.val = 1636 ∨ k.val = 1637 ∨ k.val = 1638 ∨ k.val = 1639 ∨ k.val = 1640 ∨ k.val = 1641 ∨ k.val = 1642 ∨ k.val = 1643 ∨ k.val = 1644 ∨ k.val = 1645 ∨ k.val = 1646 ∨ k.val = 1647 ∨ k.val = 1648 ∨ k.val = 1649 ∨ k.val = 1650 ∨ k.val = 1651 ∨ k.val = 1652 ∨ k.val = 1653 ∨ k.val = 1654 ∨ k.val = 1655 ∨ k.val = 1656 ∨ k.val = 1657 ∨ k.val = 1658 ∨ k.val = 1659 ∨ k.val = 1660 ∨ k.val = 1661 ∨ k.val = 1662 ∨ k.val = 1663 := by omega
  rcases heq with h1632 | h1633 | h1634 | h1635 | h1636 | h1637 | h1638 | h1639 | h1640 | h1641 | h1642 | h1643 | h1644 | h1645 | h1646 | h1647 | h1648 | h1649 | h1650 | h1651 | h1652 | h1653 | h1654 | h1655 | h1656 | h1657 | h1658 | h1659 | h1660 | h1661 | h1662 | h1663
  · have he : k = (1632 : Fin 2886) := Fin.ext h1632
    subst k
    rw [keyMomentRowsAt1632]
    exact keyMoment1632 B hB
  · have he : k = (1633 : Fin 2886) := Fin.ext h1633
    subst k
    rw [keyMomentRowsAt1633]
    exact keyMoment1633 B hB
  · have he : k = (1634 : Fin 2886) := Fin.ext h1634
    subst k
    rw [keyMomentRowsAt1634]
    exact keyMoment1634 B hB
  · have he : k = (1635 : Fin 2886) := Fin.ext h1635
    subst k
    rw [keyMomentRowsAt1635]
    exact keyMoment1635 B hB
  · have he : k = (1636 : Fin 2886) := Fin.ext h1636
    subst k
    rw [keyMomentRowsAt1636]
    exact keyMoment1636 B hB
  · have he : k = (1637 : Fin 2886) := Fin.ext h1637
    subst k
    rw [keyMomentRowsAt1637]
    exact keyMoment1637 B hB
  · have he : k = (1638 : Fin 2886) := Fin.ext h1638
    subst k
    rw [keyMomentRowsAt1638]
    exact keyMoment1638 B hB
  · have he : k = (1639 : Fin 2886) := Fin.ext h1639
    subst k
    rw [keyMomentRowsAt1639]
    exact keyMoment1639 B hB
  · have he : k = (1640 : Fin 2886) := Fin.ext h1640
    subst k
    rw [keyMomentRowsAt1640]
    exact keyMoment1640 B hB
  · have he : k = (1641 : Fin 2886) := Fin.ext h1641
    subst k
    rw [keyMomentRowsAt1641]
    exact keyMoment1641 B hB
  · have he : k = (1642 : Fin 2886) := Fin.ext h1642
    subst k
    rw [keyMomentRowsAt1642]
    exact keyMoment1642 B hB
  · have he : k = (1643 : Fin 2886) := Fin.ext h1643
    subst k
    rw [keyMomentRowsAt1643]
    exact keyMoment1643 B hB
  · have he : k = (1644 : Fin 2886) := Fin.ext h1644
    subst k
    rw [keyMomentRowsAt1644]
    exact keyMoment1644 B hB
  · have he : k = (1645 : Fin 2886) := Fin.ext h1645
    subst k
    rw [keyMomentRowsAt1645]
    exact keyMoment1645 B hB
  · have he : k = (1646 : Fin 2886) := Fin.ext h1646
    subst k
    rw [keyMomentRowsAt1646]
    exact keyMoment1646 B hB
  · have he : k = (1647 : Fin 2886) := Fin.ext h1647
    subst k
    rw [keyMomentRowsAt1647]
    exact keyMoment1647 B hB
  · have he : k = (1648 : Fin 2886) := Fin.ext h1648
    subst k
    rw [keyMomentRowsAt1648]
    exact keyMoment1648 B hB
  · have he : k = (1649 : Fin 2886) := Fin.ext h1649
    subst k
    rw [keyMomentRowsAt1649]
    exact keyMoment1649 B hB
  · have he : k = (1650 : Fin 2886) := Fin.ext h1650
    subst k
    rw [keyMomentRowsAt1650]
    exact keyMoment1650 B hB
  · have he : k = (1651 : Fin 2886) := Fin.ext h1651
    subst k
    rw [keyMomentRowsAt1651]
    exact keyMoment1651 B hB
  · have he : k = (1652 : Fin 2886) := Fin.ext h1652
    subst k
    rw [keyMomentRowsAt1652]
    exact keyMoment1652 B hB
  · have he : k = (1653 : Fin 2886) := Fin.ext h1653
    subst k
    rw [keyMomentRowsAt1653]
    exact keyMoment1653 B hB
  · have he : k = (1654 : Fin 2886) := Fin.ext h1654
    subst k
    rw [keyMomentRowsAt1654]
    exact keyMoment1654 B hB
  · have he : k = (1655 : Fin 2886) := Fin.ext h1655
    subst k
    rw [keyMomentRowsAt1655]
    exact keyMoment1655 B hB
  · have he : k = (1656 : Fin 2886) := Fin.ext h1656
    subst k
    rw [keyMomentRowsAt1656]
    exact keyMoment1656 B hB
  · have he : k = (1657 : Fin 2886) := Fin.ext h1657
    subst k
    rw [keyMomentRowsAt1657]
    exact keyMoment1657 B hB
  · have he : k = (1658 : Fin 2886) := Fin.ext h1658
    subst k
    rw [keyMomentRowsAt1658]
    exact keyMoment1658 B hB
  · have he : k = (1659 : Fin 2886) := Fin.ext h1659
    subst k
    rw [keyMomentRowsAt1659]
    exact keyMoment1659 B hB
  · have he : k = (1660 : Fin 2886) := Fin.ext h1660
    subst k
    rw [keyMomentRowsAt1660]
    exact keyMoment1660 B hB
  · have he : k = (1661 : Fin 2886) := Fin.ext h1661
    subst k
    rw [keyMomentRowsAt1661]
    exact keyMoment1661 B hB
  · have he : k = (1662 : Fin 2886) := Fin.ext h1662
    subst k
    rw [keyMomentRowsAt1662]
    exact keyMoment1662 B hB
  · have he : k = (1663 : Fin 2886) := Fin.ext h1663
    subst k
    rw [keyMomentRowsAt1663]
    exact keyMoment1663 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
