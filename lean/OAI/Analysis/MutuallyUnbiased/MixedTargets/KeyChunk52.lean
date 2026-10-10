import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound52
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1664 : keyMomentRows (1664 : Fin 2886) =
    keyMomentRow1664 := by decide +kernel

theorem keyMomentRowsAt1665 : keyMomentRows (1665 : Fin 2886) =
    keyMomentRow1665 := by decide +kernel

theorem keyMomentRowsAt1666 : keyMomentRows (1666 : Fin 2886) =
    keyMomentRow1666 := by decide +kernel

theorem keyMomentRowsAt1667 : keyMomentRows (1667 : Fin 2886) =
    keyMomentRow1667 := by decide +kernel

theorem keyMomentRowsAt1668 : keyMomentRows (1668 : Fin 2886) =
    keyMomentRow1668 := by decide +kernel

theorem keyMomentRowsAt1669 : keyMomentRows (1669 : Fin 2886) =
    keyMomentRow1669 := by decide +kernel

theorem keyMomentRowsAt1670 : keyMomentRows (1670 : Fin 2886) =
    keyMomentRow1670 := by decide +kernel

theorem keyMomentRowsAt1671 : keyMomentRows (1671 : Fin 2886) =
    keyMomentRow1671 := by decide +kernel

theorem keyMomentRowsAt1672 : keyMomentRows (1672 : Fin 2886) =
    keyMomentRow1672 := by decide +kernel

theorem keyMomentRowsAt1673 : keyMomentRows (1673 : Fin 2886) =
    keyMomentRow1673 := by decide +kernel

theorem keyMomentRowsAt1674 : keyMomentRows (1674 : Fin 2886) =
    keyMomentRow1674 := by decide +kernel

theorem keyMomentRowsAt1675 : keyMomentRows (1675 : Fin 2886) =
    keyMomentRow1675 := by decide +kernel

theorem keyMomentRowsAt1676 : keyMomentRows (1676 : Fin 2886) =
    keyMomentRow1676 := by decide +kernel

theorem keyMomentRowsAt1677 : keyMomentRows (1677 : Fin 2886) =
    keyMomentRow1677 := by decide +kernel

theorem keyMomentRowsAt1678 : keyMomentRows (1678 : Fin 2886) =
    keyMomentRow1678 := by decide +kernel

theorem keyMomentRowsAt1679 : keyMomentRows (1679 : Fin 2886) =
    keyMomentRow1679 := by decide +kernel

theorem keyMomentRowsAt1680 : keyMomentRows (1680 : Fin 2886) =
    keyMomentRow1680 := by decide +kernel

theorem keyMomentRowsAt1681 : keyMomentRows (1681 : Fin 2886) =
    keyMomentRow1681 := by decide +kernel

theorem keyMomentRowsAt1682 : keyMomentRows (1682 : Fin 2886) =
    keyMomentRow1682 := by decide +kernel

theorem keyMomentRowsAt1683 : keyMomentRows (1683 : Fin 2886) =
    keyMomentRow1683 := by decide +kernel

theorem keyMomentRowsAt1684 : keyMomentRows (1684 : Fin 2886) =
    keyMomentRow1684 := by decide +kernel

theorem keyMomentRowsAt1685 : keyMomentRows (1685 : Fin 2886) =
    keyMomentRow1685 := by decide +kernel

theorem keyMomentRowsAt1686 : keyMomentRows (1686 : Fin 2886) =
    keyMomentRow1686 := by decide +kernel

theorem keyMomentRowsAt1687 : keyMomentRows (1687 : Fin 2886) =
    keyMomentRow1687 := by decide +kernel

theorem keyMomentRowsAt1688 : keyMomentRows (1688 : Fin 2886) =
    keyMomentRow1688 := by decide +kernel

theorem keyMomentRowsAt1689 : keyMomentRows (1689 : Fin 2886) =
    keyMomentRow1689 := by decide +kernel

theorem keyMomentRowsAt1690 : keyMomentRows (1690 : Fin 2886) =
    keyMomentRow1690 := by decide +kernel

theorem keyMomentRowsAt1691 : keyMomentRows (1691 : Fin 2886) =
    keyMomentRow1691 := by decide +kernel

theorem keyMomentRowsAt1692 : keyMomentRows (1692 : Fin 2886) =
    keyMomentRow1692 := by decide +kernel

theorem keyMomentRowsAt1693 : keyMomentRows (1693 : Fin 2886) =
    keyMomentRow1693 := by decide +kernel

theorem keyMomentRowsAt1694 : keyMomentRows (1694 : Fin 2886) =
    keyMomentRow1694 := by decide +kernel

theorem keyMomentRowsAt1695 : keyMomentRows (1695 : Fin 2886) =
    keyMomentRow1695 := by decide +kernel

theorem keyMomentChunkSound52 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 52) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1664 ∨ k.val = 1665 ∨ k.val = 1666 ∨ k.val = 1667 ∨ k.val = 1668 ∨ k.val = 1669 ∨ k.val = 1670 ∨ k.val = 1671 ∨ k.val = 1672 ∨ k.val = 1673 ∨ k.val = 1674 ∨ k.val = 1675 ∨ k.val = 1676 ∨ k.val = 1677 ∨ k.val = 1678 ∨ k.val = 1679 ∨ k.val = 1680 ∨ k.val = 1681 ∨ k.val = 1682 ∨ k.val = 1683 ∨ k.val = 1684 ∨ k.val = 1685 ∨ k.val = 1686 ∨ k.val = 1687 ∨ k.val = 1688 ∨ k.val = 1689 ∨ k.val = 1690 ∨ k.val = 1691 ∨ k.val = 1692 ∨ k.val = 1693 ∨ k.val = 1694 ∨ k.val = 1695 := by omega
  rcases heq with h1664 | h1665 | h1666 | h1667 | h1668 | h1669 | h1670 | h1671 | h1672 | h1673 | h1674 | h1675 | h1676 | h1677 | h1678 | h1679 | h1680 | h1681 | h1682 | h1683 | h1684 | h1685 | h1686 | h1687 | h1688 | h1689 | h1690 | h1691 | h1692 | h1693 | h1694 | h1695
  · have he : k = (1664 : Fin 2886) := Fin.ext h1664
    subst k
    rw [keyMomentRowsAt1664]
    exact keyMoment1664 B hB
  · have he : k = (1665 : Fin 2886) := Fin.ext h1665
    subst k
    rw [keyMomentRowsAt1665]
    exact keyMoment1665 B hB
  · have he : k = (1666 : Fin 2886) := Fin.ext h1666
    subst k
    rw [keyMomentRowsAt1666]
    exact keyMoment1666 B hB
  · have he : k = (1667 : Fin 2886) := Fin.ext h1667
    subst k
    rw [keyMomentRowsAt1667]
    exact keyMoment1667 B hB
  · have he : k = (1668 : Fin 2886) := Fin.ext h1668
    subst k
    rw [keyMomentRowsAt1668]
    exact keyMoment1668 B hB
  · have he : k = (1669 : Fin 2886) := Fin.ext h1669
    subst k
    rw [keyMomentRowsAt1669]
    exact keyMoment1669 B hB
  · have he : k = (1670 : Fin 2886) := Fin.ext h1670
    subst k
    rw [keyMomentRowsAt1670]
    exact keyMoment1670 B hB
  · have he : k = (1671 : Fin 2886) := Fin.ext h1671
    subst k
    rw [keyMomentRowsAt1671]
    exact keyMoment1671 B hB
  · have he : k = (1672 : Fin 2886) := Fin.ext h1672
    subst k
    rw [keyMomentRowsAt1672]
    exact keyMoment1672 B hB
  · have he : k = (1673 : Fin 2886) := Fin.ext h1673
    subst k
    rw [keyMomentRowsAt1673]
    exact keyMoment1673 B hB
  · have he : k = (1674 : Fin 2886) := Fin.ext h1674
    subst k
    rw [keyMomentRowsAt1674]
    exact keyMoment1674 B hB
  · have he : k = (1675 : Fin 2886) := Fin.ext h1675
    subst k
    rw [keyMomentRowsAt1675]
    exact keyMoment1675 B hB
  · have he : k = (1676 : Fin 2886) := Fin.ext h1676
    subst k
    rw [keyMomentRowsAt1676]
    exact keyMoment1676 B hB
  · have he : k = (1677 : Fin 2886) := Fin.ext h1677
    subst k
    rw [keyMomentRowsAt1677]
    exact keyMoment1677 B hB
  · have he : k = (1678 : Fin 2886) := Fin.ext h1678
    subst k
    rw [keyMomentRowsAt1678]
    exact keyMoment1678 B hB
  · have he : k = (1679 : Fin 2886) := Fin.ext h1679
    subst k
    rw [keyMomentRowsAt1679]
    exact keyMoment1679 B hB
  · have he : k = (1680 : Fin 2886) := Fin.ext h1680
    subst k
    rw [keyMomentRowsAt1680]
    exact keyMoment1680 B hB
  · have he : k = (1681 : Fin 2886) := Fin.ext h1681
    subst k
    rw [keyMomentRowsAt1681]
    exact keyMoment1681 B hB
  · have he : k = (1682 : Fin 2886) := Fin.ext h1682
    subst k
    rw [keyMomentRowsAt1682]
    exact keyMoment1682 B hB
  · have he : k = (1683 : Fin 2886) := Fin.ext h1683
    subst k
    rw [keyMomentRowsAt1683]
    exact keyMoment1683 B hB
  · have he : k = (1684 : Fin 2886) := Fin.ext h1684
    subst k
    rw [keyMomentRowsAt1684]
    exact keyMoment1684 B hB
  · have he : k = (1685 : Fin 2886) := Fin.ext h1685
    subst k
    rw [keyMomentRowsAt1685]
    exact keyMoment1685 B hB
  · have he : k = (1686 : Fin 2886) := Fin.ext h1686
    subst k
    rw [keyMomentRowsAt1686]
    exact keyMoment1686 B hB
  · have he : k = (1687 : Fin 2886) := Fin.ext h1687
    subst k
    rw [keyMomentRowsAt1687]
    exact keyMoment1687 B hB
  · have he : k = (1688 : Fin 2886) := Fin.ext h1688
    subst k
    rw [keyMomentRowsAt1688]
    exact keyMoment1688 B hB
  · have he : k = (1689 : Fin 2886) := Fin.ext h1689
    subst k
    rw [keyMomentRowsAt1689]
    exact keyMoment1689 B hB
  · have he : k = (1690 : Fin 2886) := Fin.ext h1690
    subst k
    rw [keyMomentRowsAt1690]
    exact keyMoment1690 B hB
  · have he : k = (1691 : Fin 2886) := Fin.ext h1691
    subst k
    rw [keyMomentRowsAt1691]
    exact keyMoment1691 B hB
  · have he : k = (1692 : Fin 2886) := Fin.ext h1692
    subst k
    rw [keyMomentRowsAt1692]
    exact keyMoment1692 B hB
  · have he : k = (1693 : Fin 2886) := Fin.ext h1693
    subst k
    rw [keyMomentRowsAt1693]
    exact keyMoment1693 B hB
  · have he : k = (1694 : Fin 2886) := Fin.ext h1694
    subst k
    rw [keyMomentRowsAt1694]
    exact keyMoment1694 B hB
  · have he : k = (1695 : Fin 2886) := Fin.ext h1695
    subst k
    rw [keyMomentRowsAt1695]
    exact keyMoment1695 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
