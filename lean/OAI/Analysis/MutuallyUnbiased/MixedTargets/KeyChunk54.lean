import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound54
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1728 : keyMomentRows (1728 : Fin 2886) =
    keyMomentRow1728 := by decide +kernel

theorem keyMomentRowsAt1729 : keyMomentRows (1729 : Fin 2886) =
    keyMomentRow1729 := by decide +kernel

theorem keyMomentRowsAt1730 : keyMomentRows (1730 : Fin 2886) =
    keyMomentRow1730 := by decide +kernel

theorem keyMomentRowsAt1731 : keyMomentRows (1731 : Fin 2886) =
    keyMomentRow1731 := by decide +kernel

theorem keyMomentRowsAt1732 : keyMomentRows (1732 : Fin 2886) =
    keyMomentRow1732 := by decide +kernel

theorem keyMomentRowsAt1733 : keyMomentRows (1733 : Fin 2886) =
    keyMomentRow1733 := by decide +kernel

theorem keyMomentRowsAt1734 : keyMomentRows (1734 : Fin 2886) =
    keyMomentRow1734 := by decide +kernel

theorem keyMomentRowsAt1735 : keyMomentRows (1735 : Fin 2886) =
    keyMomentRow1735 := by decide +kernel

theorem keyMomentRowsAt1736 : keyMomentRows (1736 : Fin 2886) =
    keyMomentRow1736 := by decide +kernel

theorem keyMomentRowsAt1737 : keyMomentRows (1737 : Fin 2886) =
    keyMomentRow1737 := by decide +kernel

theorem keyMomentRowsAt1738 : keyMomentRows (1738 : Fin 2886) =
    keyMomentRow1738 := by decide +kernel

theorem keyMomentRowsAt1739 : keyMomentRows (1739 : Fin 2886) =
    keyMomentRow1739 := by decide +kernel

theorem keyMomentRowsAt1740 : keyMomentRows (1740 : Fin 2886) =
    keyMomentRow1740 := by decide +kernel

theorem keyMomentRowsAt1741 : keyMomentRows (1741 : Fin 2886) =
    keyMomentRow1741 := by decide +kernel

theorem keyMomentRowsAt1742 : keyMomentRows (1742 : Fin 2886) =
    keyMomentRow1742 := by decide +kernel

theorem keyMomentRowsAt1743 : keyMomentRows (1743 : Fin 2886) =
    keyMomentRow1743 := by decide +kernel

theorem keyMomentRowsAt1744 : keyMomentRows (1744 : Fin 2886) =
    keyMomentRow1744 := by decide +kernel

theorem keyMomentRowsAt1745 : keyMomentRows (1745 : Fin 2886) =
    keyMomentRow1745 := by decide +kernel

theorem keyMomentRowsAt1746 : keyMomentRows (1746 : Fin 2886) =
    keyMomentRow1746 := by decide +kernel

theorem keyMomentRowsAt1747 : keyMomentRows (1747 : Fin 2886) =
    keyMomentRow1747 := by decide +kernel

theorem keyMomentRowsAt1748 : keyMomentRows (1748 : Fin 2886) =
    keyMomentRow1748 := by decide +kernel

theorem keyMomentRowsAt1749 : keyMomentRows (1749 : Fin 2886) =
    keyMomentRow1749 := by decide +kernel

theorem keyMomentRowsAt1750 : keyMomentRows (1750 : Fin 2886) =
    keyMomentRow1750 := by decide +kernel

theorem keyMomentRowsAt1751 : keyMomentRows (1751 : Fin 2886) =
    keyMomentRow1751 := by decide +kernel

theorem keyMomentRowsAt1752 : keyMomentRows (1752 : Fin 2886) =
    keyMomentRow1752 := by decide +kernel

theorem keyMomentRowsAt1753 : keyMomentRows (1753 : Fin 2886) =
    keyMomentRow1753 := by decide +kernel

theorem keyMomentRowsAt1754 : keyMomentRows (1754 : Fin 2886) =
    keyMomentRow1754 := by decide +kernel

theorem keyMomentRowsAt1755 : keyMomentRows (1755 : Fin 2886) =
    keyMomentRow1755 := by decide +kernel

theorem keyMomentRowsAt1756 : keyMomentRows (1756 : Fin 2886) =
    keyMomentRow1756 := by decide +kernel

theorem keyMomentRowsAt1757 : keyMomentRows (1757 : Fin 2886) =
    keyMomentRow1757 := by decide +kernel

theorem keyMomentRowsAt1758 : keyMomentRows (1758 : Fin 2886) =
    keyMomentRow1758 := by decide +kernel

theorem keyMomentRowsAt1759 : keyMomentRows (1759 : Fin 2886) =
    keyMomentRow1759 := by decide +kernel

theorem keyMomentChunkSound54 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 54) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1728 ∨ k.val = 1729 ∨ k.val = 1730 ∨ k.val = 1731 ∨ k.val = 1732 ∨ k.val = 1733 ∨ k.val = 1734 ∨ k.val = 1735 ∨ k.val = 1736 ∨ k.val = 1737 ∨ k.val = 1738 ∨ k.val = 1739 ∨ k.val = 1740 ∨ k.val = 1741 ∨ k.val = 1742 ∨ k.val = 1743 ∨ k.val = 1744 ∨ k.val = 1745 ∨ k.val = 1746 ∨ k.val = 1747 ∨ k.val = 1748 ∨ k.val = 1749 ∨ k.val = 1750 ∨ k.val = 1751 ∨ k.val = 1752 ∨ k.val = 1753 ∨ k.val = 1754 ∨ k.val = 1755 ∨ k.val = 1756 ∨ k.val = 1757 ∨ k.val = 1758 ∨ k.val = 1759 := by omega
  rcases heq with h1728 | h1729 | h1730 | h1731 | h1732 | h1733 | h1734 | h1735 | h1736 | h1737 | h1738 | h1739 | h1740 | h1741 | h1742 | h1743 | h1744 | h1745 | h1746 | h1747 | h1748 | h1749 | h1750 | h1751 | h1752 | h1753 | h1754 | h1755 | h1756 | h1757 | h1758 | h1759
  · have he : k = (1728 : Fin 2886) := Fin.ext h1728
    subst k
    rw [keyMomentRowsAt1728]
    exact keyMoment1728 B hB
  · have he : k = (1729 : Fin 2886) := Fin.ext h1729
    subst k
    rw [keyMomentRowsAt1729]
    exact keyMoment1729 B hB
  · have he : k = (1730 : Fin 2886) := Fin.ext h1730
    subst k
    rw [keyMomentRowsAt1730]
    exact keyMoment1730 B hB
  · have he : k = (1731 : Fin 2886) := Fin.ext h1731
    subst k
    rw [keyMomentRowsAt1731]
    exact keyMoment1731 B hB
  · have he : k = (1732 : Fin 2886) := Fin.ext h1732
    subst k
    rw [keyMomentRowsAt1732]
    exact keyMoment1732 B hB
  · have he : k = (1733 : Fin 2886) := Fin.ext h1733
    subst k
    rw [keyMomentRowsAt1733]
    exact keyMoment1733 B hB
  · have he : k = (1734 : Fin 2886) := Fin.ext h1734
    subst k
    rw [keyMomentRowsAt1734]
    exact keyMoment1734 B hB
  · have he : k = (1735 : Fin 2886) := Fin.ext h1735
    subst k
    rw [keyMomentRowsAt1735]
    exact keyMoment1735 B hB
  · have he : k = (1736 : Fin 2886) := Fin.ext h1736
    subst k
    rw [keyMomentRowsAt1736]
    exact keyMoment1736 B hB
  · have he : k = (1737 : Fin 2886) := Fin.ext h1737
    subst k
    rw [keyMomentRowsAt1737]
    exact keyMoment1737 B hB
  · have he : k = (1738 : Fin 2886) := Fin.ext h1738
    subst k
    rw [keyMomentRowsAt1738]
    exact keyMoment1738 B hB
  · have he : k = (1739 : Fin 2886) := Fin.ext h1739
    subst k
    rw [keyMomentRowsAt1739]
    exact keyMoment1739 B hB
  · have he : k = (1740 : Fin 2886) := Fin.ext h1740
    subst k
    rw [keyMomentRowsAt1740]
    exact keyMoment1740 B hB
  · have he : k = (1741 : Fin 2886) := Fin.ext h1741
    subst k
    rw [keyMomentRowsAt1741]
    exact keyMoment1741 B hB
  · have he : k = (1742 : Fin 2886) := Fin.ext h1742
    subst k
    rw [keyMomentRowsAt1742]
    exact keyMoment1742 B hB
  · have he : k = (1743 : Fin 2886) := Fin.ext h1743
    subst k
    rw [keyMomentRowsAt1743]
    exact keyMoment1743 B hB
  · have he : k = (1744 : Fin 2886) := Fin.ext h1744
    subst k
    rw [keyMomentRowsAt1744]
    exact keyMoment1744 B hB
  · have he : k = (1745 : Fin 2886) := Fin.ext h1745
    subst k
    rw [keyMomentRowsAt1745]
    exact keyMoment1745 B hB
  · have he : k = (1746 : Fin 2886) := Fin.ext h1746
    subst k
    rw [keyMomentRowsAt1746]
    exact keyMoment1746 B hB
  · have he : k = (1747 : Fin 2886) := Fin.ext h1747
    subst k
    rw [keyMomentRowsAt1747]
    exact keyMoment1747 B hB
  · have he : k = (1748 : Fin 2886) := Fin.ext h1748
    subst k
    rw [keyMomentRowsAt1748]
    exact keyMoment1748 B hB
  · have he : k = (1749 : Fin 2886) := Fin.ext h1749
    subst k
    rw [keyMomentRowsAt1749]
    exact keyMoment1749 B hB
  · have he : k = (1750 : Fin 2886) := Fin.ext h1750
    subst k
    rw [keyMomentRowsAt1750]
    exact keyMoment1750 B hB
  · have he : k = (1751 : Fin 2886) := Fin.ext h1751
    subst k
    rw [keyMomentRowsAt1751]
    exact keyMoment1751 B hB
  · have he : k = (1752 : Fin 2886) := Fin.ext h1752
    subst k
    rw [keyMomentRowsAt1752]
    exact keyMoment1752 B hB
  · have he : k = (1753 : Fin 2886) := Fin.ext h1753
    subst k
    rw [keyMomentRowsAt1753]
    exact keyMoment1753 B hB
  · have he : k = (1754 : Fin 2886) := Fin.ext h1754
    subst k
    rw [keyMomentRowsAt1754]
    exact keyMoment1754 B hB
  · have he : k = (1755 : Fin 2886) := Fin.ext h1755
    subst k
    rw [keyMomentRowsAt1755]
    exact keyMoment1755 B hB
  · have he : k = (1756 : Fin 2886) := Fin.ext h1756
    subst k
    rw [keyMomentRowsAt1756]
    exact keyMoment1756 B hB
  · have he : k = (1757 : Fin 2886) := Fin.ext h1757
    subst k
    rw [keyMomentRowsAt1757]
    exact keyMoment1757 B hB
  · have he : k = (1758 : Fin 2886) := Fin.ext h1758
    subst k
    rw [keyMomentRowsAt1758]
    exact keyMoment1758 B hB
  · have he : k = (1759 : Fin 2886) := Fin.ext h1759
    subst k
    rw [keyMomentRowsAt1759]
    exact keyMoment1759 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
