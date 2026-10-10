import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound55
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1760 : keyMomentRows (1760 : Fin 2886) =
    keyMomentRow1760 := by decide +kernel

theorem keyMomentRowsAt1761 : keyMomentRows (1761 : Fin 2886) =
    keyMomentRow1761 := by decide +kernel

theorem keyMomentRowsAt1762 : keyMomentRows (1762 : Fin 2886) =
    keyMomentRow1762 := by decide +kernel

theorem keyMomentRowsAt1763 : keyMomentRows (1763 : Fin 2886) =
    keyMomentRow1763 := by decide +kernel

theorem keyMomentRowsAt1764 : keyMomentRows (1764 : Fin 2886) =
    keyMomentRow1764 := by decide +kernel

theorem keyMomentRowsAt1765 : keyMomentRows (1765 : Fin 2886) =
    keyMomentRow1765 := by decide +kernel

theorem keyMomentRowsAt1766 : keyMomentRows (1766 : Fin 2886) =
    keyMomentRow1766 := by decide +kernel

theorem keyMomentRowsAt1767 : keyMomentRows (1767 : Fin 2886) =
    keyMomentRow1767 := by decide +kernel

theorem keyMomentRowsAt1768 : keyMomentRows (1768 : Fin 2886) =
    keyMomentRow1768 := by decide +kernel

theorem keyMomentRowsAt1769 : keyMomentRows (1769 : Fin 2886) =
    keyMomentRow1769 := by decide +kernel

theorem keyMomentRowsAt1770 : keyMomentRows (1770 : Fin 2886) =
    keyMomentRow1770 := by decide +kernel

theorem keyMomentRowsAt1771 : keyMomentRows (1771 : Fin 2886) =
    keyMomentRow1771 := by decide +kernel

theorem keyMomentRowsAt1772 : keyMomentRows (1772 : Fin 2886) =
    keyMomentRow1772 := by decide +kernel

theorem keyMomentRowsAt1773 : keyMomentRows (1773 : Fin 2886) =
    keyMomentRow1773 := by decide +kernel

theorem keyMomentRowsAt1774 : keyMomentRows (1774 : Fin 2886) =
    keyMomentRow1774 := by decide +kernel

theorem keyMomentRowsAt1775 : keyMomentRows (1775 : Fin 2886) =
    keyMomentRow1775 := by decide +kernel

theorem keyMomentRowsAt1776 : keyMomentRows (1776 : Fin 2886) =
    keyMomentRow1776 := by decide +kernel

theorem keyMomentRowsAt1777 : keyMomentRows (1777 : Fin 2886) =
    keyMomentRow1777 := by decide +kernel

theorem keyMomentRowsAt1778 : keyMomentRows (1778 : Fin 2886) =
    keyMomentRow1778 := by decide +kernel

theorem keyMomentRowsAt1779 : keyMomentRows (1779 : Fin 2886) =
    keyMomentRow1779 := by decide +kernel

theorem keyMomentRowsAt1780 : keyMomentRows (1780 : Fin 2886) =
    keyMomentRow1780 := by decide +kernel

theorem keyMomentRowsAt1781 : keyMomentRows (1781 : Fin 2886) =
    keyMomentRow1781 := by decide +kernel

theorem keyMomentRowsAt1782 : keyMomentRows (1782 : Fin 2886) =
    keyMomentRow1782 := by decide +kernel

theorem keyMomentRowsAt1783 : keyMomentRows (1783 : Fin 2886) =
    keyMomentRow1783 := by decide +kernel

theorem keyMomentRowsAt1784 : keyMomentRows (1784 : Fin 2886) =
    keyMomentRow1784 := by decide +kernel

theorem keyMomentRowsAt1785 : keyMomentRows (1785 : Fin 2886) =
    keyMomentRow1785 := by decide +kernel

theorem keyMomentRowsAt1786 : keyMomentRows (1786 : Fin 2886) =
    keyMomentRow1786 := by decide +kernel

theorem keyMomentRowsAt1787 : keyMomentRows (1787 : Fin 2886) =
    keyMomentRow1787 := by decide +kernel

theorem keyMomentRowsAt1788 : keyMomentRows (1788 : Fin 2886) =
    keyMomentRow1788 := by decide +kernel

theorem keyMomentRowsAt1789 : keyMomentRows (1789 : Fin 2886) =
    keyMomentRow1789 := by decide +kernel

theorem keyMomentRowsAt1790 : keyMomentRows (1790 : Fin 2886) =
    keyMomentRow1790 := by decide +kernel

theorem keyMomentRowsAt1791 : keyMomentRows (1791 : Fin 2886) =
    keyMomentRow1791 := by decide +kernel

theorem keyMomentChunkSound55 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 55) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1760 ∨ k.val = 1761 ∨ k.val = 1762 ∨ k.val = 1763 ∨ k.val = 1764 ∨ k.val = 1765 ∨ k.val = 1766 ∨ k.val = 1767 ∨ k.val = 1768 ∨ k.val = 1769 ∨ k.val = 1770 ∨ k.val = 1771 ∨ k.val = 1772 ∨ k.val = 1773 ∨ k.val = 1774 ∨ k.val = 1775 ∨ k.val = 1776 ∨ k.val = 1777 ∨ k.val = 1778 ∨ k.val = 1779 ∨ k.val = 1780 ∨ k.val = 1781 ∨ k.val = 1782 ∨ k.val = 1783 ∨ k.val = 1784 ∨ k.val = 1785 ∨ k.val = 1786 ∨ k.val = 1787 ∨ k.val = 1788 ∨ k.val = 1789 ∨ k.val = 1790 ∨ k.val = 1791 := by omega
  rcases heq with h1760 | h1761 | h1762 | h1763 | h1764 | h1765 | h1766 | h1767 | h1768 | h1769 | h1770 | h1771 | h1772 | h1773 | h1774 | h1775 | h1776 | h1777 | h1778 | h1779 | h1780 | h1781 | h1782 | h1783 | h1784 | h1785 | h1786 | h1787 | h1788 | h1789 | h1790 | h1791
  · have he : k = (1760 : Fin 2886) := Fin.ext h1760
    subst k
    rw [keyMomentRowsAt1760]
    exact keyMoment1760 B hB
  · have he : k = (1761 : Fin 2886) := Fin.ext h1761
    subst k
    rw [keyMomentRowsAt1761]
    exact keyMoment1761 B hB
  · have he : k = (1762 : Fin 2886) := Fin.ext h1762
    subst k
    rw [keyMomentRowsAt1762]
    exact keyMoment1762 B hB
  · have he : k = (1763 : Fin 2886) := Fin.ext h1763
    subst k
    rw [keyMomentRowsAt1763]
    exact keyMoment1763 B hB
  · have he : k = (1764 : Fin 2886) := Fin.ext h1764
    subst k
    rw [keyMomentRowsAt1764]
    exact keyMoment1764 B hB
  · have he : k = (1765 : Fin 2886) := Fin.ext h1765
    subst k
    rw [keyMomentRowsAt1765]
    exact keyMoment1765 B hB
  · have he : k = (1766 : Fin 2886) := Fin.ext h1766
    subst k
    rw [keyMomentRowsAt1766]
    exact keyMoment1766 B hB
  · have he : k = (1767 : Fin 2886) := Fin.ext h1767
    subst k
    rw [keyMomentRowsAt1767]
    exact keyMoment1767 B hB
  · have he : k = (1768 : Fin 2886) := Fin.ext h1768
    subst k
    rw [keyMomentRowsAt1768]
    exact keyMoment1768 B hB
  · have he : k = (1769 : Fin 2886) := Fin.ext h1769
    subst k
    rw [keyMomentRowsAt1769]
    exact keyMoment1769 B hB
  · have he : k = (1770 : Fin 2886) := Fin.ext h1770
    subst k
    rw [keyMomentRowsAt1770]
    exact keyMoment1770 B hB
  · have he : k = (1771 : Fin 2886) := Fin.ext h1771
    subst k
    rw [keyMomentRowsAt1771]
    exact keyMoment1771 B hB
  · have he : k = (1772 : Fin 2886) := Fin.ext h1772
    subst k
    rw [keyMomentRowsAt1772]
    exact keyMoment1772 B hB
  · have he : k = (1773 : Fin 2886) := Fin.ext h1773
    subst k
    rw [keyMomentRowsAt1773]
    exact keyMoment1773 B hB
  · have he : k = (1774 : Fin 2886) := Fin.ext h1774
    subst k
    rw [keyMomentRowsAt1774]
    exact keyMoment1774 B hB
  · have he : k = (1775 : Fin 2886) := Fin.ext h1775
    subst k
    rw [keyMomentRowsAt1775]
    exact keyMoment1775 B hB
  · have he : k = (1776 : Fin 2886) := Fin.ext h1776
    subst k
    rw [keyMomentRowsAt1776]
    exact keyMoment1776 B hB
  · have he : k = (1777 : Fin 2886) := Fin.ext h1777
    subst k
    rw [keyMomentRowsAt1777]
    exact keyMoment1777 B hB
  · have he : k = (1778 : Fin 2886) := Fin.ext h1778
    subst k
    rw [keyMomentRowsAt1778]
    exact keyMoment1778 B hB
  · have he : k = (1779 : Fin 2886) := Fin.ext h1779
    subst k
    rw [keyMomentRowsAt1779]
    exact keyMoment1779 B hB
  · have he : k = (1780 : Fin 2886) := Fin.ext h1780
    subst k
    rw [keyMomentRowsAt1780]
    exact keyMoment1780 B hB
  · have he : k = (1781 : Fin 2886) := Fin.ext h1781
    subst k
    rw [keyMomentRowsAt1781]
    exact keyMoment1781 B hB
  · have he : k = (1782 : Fin 2886) := Fin.ext h1782
    subst k
    rw [keyMomentRowsAt1782]
    exact keyMoment1782 B hB
  · have he : k = (1783 : Fin 2886) := Fin.ext h1783
    subst k
    rw [keyMomentRowsAt1783]
    exact keyMoment1783 B hB
  · have he : k = (1784 : Fin 2886) := Fin.ext h1784
    subst k
    rw [keyMomentRowsAt1784]
    exact keyMoment1784 B hB
  · have he : k = (1785 : Fin 2886) := Fin.ext h1785
    subst k
    rw [keyMomentRowsAt1785]
    exact keyMoment1785 B hB
  · have he : k = (1786 : Fin 2886) := Fin.ext h1786
    subst k
    rw [keyMomentRowsAt1786]
    exact keyMoment1786 B hB
  · have he : k = (1787 : Fin 2886) := Fin.ext h1787
    subst k
    rw [keyMomentRowsAt1787]
    exact keyMoment1787 B hB
  · have he : k = (1788 : Fin 2886) := Fin.ext h1788
    subst k
    rw [keyMomentRowsAt1788]
    exact keyMoment1788 B hB
  · have he : k = (1789 : Fin 2886) := Fin.ext h1789
    subst k
    rw [keyMomentRowsAt1789]
    exact keyMoment1789 B hB
  · have he : k = (1790 : Fin 2886) := Fin.ext h1790
    subst k
    rw [keyMomentRowsAt1790]
    exact keyMoment1790 B hB
  · have he : k = (1791 : Fin 2886) := Fin.ext h1791
    subst k
    rw [keyMomentRowsAt1791]
    exact keyMoment1791 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
