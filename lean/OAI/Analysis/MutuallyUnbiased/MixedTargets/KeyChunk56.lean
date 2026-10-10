import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound56
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1792 : keyMomentRows (1792 : Fin 2886) =
    keyMomentRow1792 := by decide +kernel

theorem keyMomentRowsAt1793 : keyMomentRows (1793 : Fin 2886) =
    keyMomentRow1793 := by decide +kernel

theorem keyMomentRowsAt1794 : keyMomentRows (1794 : Fin 2886) =
    keyMomentRow1794 := by decide +kernel

theorem keyMomentRowsAt1795 : keyMomentRows (1795 : Fin 2886) =
    keyMomentRow1795 := by decide +kernel

theorem keyMomentRowsAt1796 : keyMomentRows (1796 : Fin 2886) =
    keyMomentRow1796 := by decide +kernel

theorem keyMomentRowsAt1797 : keyMomentRows (1797 : Fin 2886) =
    keyMomentRow1797 := by decide +kernel

theorem keyMomentRowsAt1798 : keyMomentRows (1798 : Fin 2886) =
    keyMomentRow1798 := by decide +kernel

theorem keyMomentRowsAt1799 : keyMomentRows (1799 : Fin 2886) =
    keyMomentRow1799 := by decide +kernel

theorem keyMomentRowsAt1800 : keyMomentRows (1800 : Fin 2886) =
    keyMomentRow1800 := by decide +kernel

theorem keyMomentRowsAt1801 : keyMomentRows (1801 : Fin 2886) =
    keyMomentRow1801 := by decide +kernel

theorem keyMomentRowsAt1802 : keyMomentRows (1802 : Fin 2886) =
    keyMomentRow1802 := by decide +kernel

theorem keyMomentRowsAt1803 : keyMomentRows (1803 : Fin 2886) =
    keyMomentRow1803 := by decide +kernel

theorem keyMomentRowsAt1804 : keyMomentRows (1804 : Fin 2886) =
    keyMomentRow1804 := by decide +kernel

theorem keyMomentRowsAt1805 : keyMomentRows (1805 : Fin 2886) =
    keyMomentRow1805 := by decide +kernel

theorem keyMomentRowsAt1806 : keyMomentRows (1806 : Fin 2886) =
    keyMomentRow1806 := by decide +kernel

theorem keyMomentRowsAt1807 : keyMomentRows (1807 : Fin 2886) =
    keyMomentRow1807 := by decide +kernel

theorem keyMomentRowsAt1808 : keyMomentRows (1808 : Fin 2886) =
    keyMomentRow1808 := by decide +kernel

theorem keyMomentRowsAt1809 : keyMomentRows (1809 : Fin 2886) =
    keyMomentRow1809 := by decide +kernel

theorem keyMomentRowsAt1810 : keyMomentRows (1810 : Fin 2886) =
    keyMomentRow1810 := by decide +kernel

theorem keyMomentRowsAt1811 : keyMomentRows (1811 : Fin 2886) =
    keyMomentRow1811 := by decide +kernel

theorem keyMomentRowsAt1812 : keyMomentRows (1812 : Fin 2886) =
    keyMomentRow1812 := by decide +kernel

theorem keyMomentRowsAt1813 : keyMomentRows (1813 : Fin 2886) =
    keyMomentRow1813 := by decide +kernel

theorem keyMomentRowsAt1814 : keyMomentRows (1814 : Fin 2886) =
    keyMomentRow1814 := by decide +kernel

theorem keyMomentRowsAt1815 : keyMomentRows (1815 : Fin 2886) =
    keyMomentRow1815 := by decide +kernel

theorem keyMomentRowsAt1816 : keyMomentRows (1816 : Fin 2886) =
    keyMomentRow1816 := by decide +kernel

theorem keyMomentRowsAt1817 : keyMomentRows (1817 : Fin 2886) =
    keyMomentRow1817 := by decide +kernel

theorem keyMomentRowsAt1818 : keyMomentRows (1818 : Fin 2886) =
    keyMomentRow1818 := by decide +kernel

theorem keyMomentRowsAt1819 : keyMomentRows (1819 : Fin 2886) =
    keyMomentRow1819 := by decide +kernel

theorem keyMomentRowsAt1820 : keyMomentRows (1820 : Fin 2886) =
    keyMomentRow1820 := by decide +kernel

theorem keyMomentRowsAt1821 : keyMomentRows (1821 : Fin 2886) =
    keyMomentRow1821 := by decide +kernel

theorem keyMomentRowsAt1822 : keyMomentRows (1822 : Fin 2886) =
    keyMomentRow1822 := by decide +kernel

theorem keyMomentRowsAt1823 : keyMomentRows (1823 : Fin 2886) =
    keyMomentRow1823 := by decide +kernel

theorem keyMomentChunkSound56 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 56) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1792 ∨ k.val = 1793 ∨ k.val = 1794 ∨ k.val = 1795 ∨ k.val = 1796 ∨ k.val = 1797 ∨ k.val = 1798 ∨ k.val = 1799 ∨ k.val = 1800 ∨ k.val = 1801 ∨ k.val = 1802 ∨ k.val = 1803 ∨ k.val = 1804 ∨ k.val = 1805 ∨ k.val = 1806 ∨ k.val = 1807 ∨ k.val = 1808 ∨ k.val = 1809 ∨ k.val = 1810 ∨ k.val = 1811 ∨ k.val = 1812 ∨ k.val = 1813 ∨ k.val = 1814 ∨ k.val = 1815 ∨ k.val = 1816 ∨ k.val = 1817 ∨ k.val = 1818 ∨ k.val = 1819 ∨ k.val = 1820 ∨ k.val = 1821 ∨ k.val = 1822 ∨ k.val = 1823 := by omega
  rcases heq with h1792 | h1793 | h1794 | h1795 | h1796 | h1797 | h1798 | h1799 | h1800 | h1801 | h1802 | h1803 | h1804 | h1805 | h1806 | h1807 | h1808 | h1809 | h1810 | h1811 | h1812 | h1813 | h1814 | h1815 | h1816 | h1817 | h1818 | h1819 | h1820 | h1821 | h1822 | h1823
  · have he : k = (1792 : Fin 2886) := Fin.ext h1792
    subst k
    rw [keyMomentRowsAt1792]
    exact keyMoment1792 B hB
  · have he : k = (1793 : Fin 2886) := Fin.ext h1793
    subst k
    rw [keyMomentRowsAt1793]
    exact keyMoment1793 B hB
  · have he : k = (1794 : Fin 2886) := Fin.ext h1794
    subst k
    rw [keyMomentRowsAt1794]
    exact keyMoment1794 B hB
  · have he : k = (1795 : Fin 2886) := Fin.ext h1795
    subst k
    rw [keyMomentRowsAt1795]
    exact keyMoment1795 B hB
  · have he : k = (1796 : Fin 2886) := Fin.ext h1796
    subst k
    rw [keyMomentRowsAt1796]
    exact keyMoment1796 B hB
  · have he : k = (1797 : Fin 2886) := Fin.ext h1797
    subst k
    rw [keyMomentRowsAt1797]
    exact keyMoment1797 B hB
  · have he : k = (1798 : Fin 2886) := Fin.ext h1798
    subst k
    rw [keyMomentRowsAt1798]
    exact keyMoment1798 B hB
  · have he : k = (1799 : Fin 2886) := Fin.ext h1799
    subst k
    rw [keyMomentRowsAt1799]
    exact keyMoment1799 B hB
  · have he : k = (1800 : Fin 2886) := Fin.ext h1800
    subst k
    rw [keyMomentRowsAt1800]
    exact keyMoment1800 B hB
  · have he : k = (1801 : Fin 2886) := Fin.ext h1801
    subst k
    rw [keyMomentRowsAt1801]
    exact keyMoment1801 B hB
  · have he : k = (1802 : Fin 2886) := Fin.ext h1802
    subst k
    rw [keyMomentRowsAt1802]
    exact keyMoment1802 B hB
  · have he : k = (1803 : Fin 2886) := Fin.ext h1803
    subst k
    rw [keyMomentRowsAt1803]
    exact keyMoment1803 B hB
  · have he : k = (1804 : Fin 2886) := Fin.ext h1804
    subst k
    rw [keyMomentRowsAt1804]
    exact keyMoment1804 B hB
  · have he : k = (1805 : Fin 2886) := Fin.ext h1805
    subst k
    rw [keyMomentRowsAt1805]
    exact keyMoment1805 B hB
  · have he : k = (1806 : Fin 2886) := Fin.ext h1806
    subst k
    rw [keyMomentRowsAt1806]
    exact keyMoment1806 B hB
  · have he : k = (1807 : Fin 2886) := Fin.ext h1807
    subst k
    rw [keyMomentRowsAt1807]
    exact keyMoment1807 B hB
  · have he : k = (1808 : Fin 2886) := Fin.ext h1808
    subst k
    rw [keyMomentRowsAt1808]
    exact keyMoment1808 B hB
  · have he : k = (1809 : Fin 2886) := Fin.ext h1809
    subst k
    rw [keyMomentRowsAt1809]
    exact keyMoment1809 B hB
  · have he : k = (1810 : Fin 2886) := Fin.ext h1810
    subst k
    rw [keyMomentRowsAt1810]
    exact keyMoment1810 B hB
  · have he : k = (1811 : Fin 2886) := Fin.ext h1811
    subst k
    rw [keyMomentRowsAt1811]
    exact keyMoment1811 B hB
  · have he : k = (1812 : Fin 2886) := Fin.ext h1812
    subst k
    rw [keyMomentRowsAt1812]
    exact keyMoment1812 B hB
  · have he : k = (1813 : Fin 2886) := Fin.ext h1813
    subst k
    rw [keyMomentRowsAt1813]
    exact keyMoment1813 B hB
  · have he : k = (1814 : Fin 2886) := Fin.ext h1814
    subst k
    rw [keyMomentRowsAt1814]
    exact keyMoment1814 B hB
  · have he : k = (1815 : Fin 2886) := Fin.ext h1815
    subst k
    rw [keyMomentRowsAt1815]
    exact keyMoment1815 B hB
  · have he : k = (1816 : Fin 2886) := Fin.ext h1816
    subst k
    rw [keyMomentRowsAt1816]
    exact keyMoment1816 B hB
  · have he : k = (1817 : Fin 2886) := Fin.ext h1817
    subst k
    rw [keyMomentRowsAt1817]
    exact keyMoment1817 B hB
  · have he : k = (1818 : Fin 2886) := Fin.ext h1818
    subst k
    rw [keyMomentRowsAt1818]
    exact keyMoment1818 B hB
  · have he : k = (1819 : Fin 2886) := Fin.ext h1819
    subst k
    rw [keyMomentRowsAt1819]
    exact keyMoment1819 B hB
  · have he : k = (1820 : Fin 2886) := Fin.ext h1820
    subst k
    rw [keyMomentRowsAt1820]
    exact keyMoment1820 B hB
  · have he : k = (1821 : Fin 2886) := Fin.ext h1821
    subst k
    rw [keyMomentRowsAt1821]
    exact keyMoment1821 B hB
  · have he : k = (1822 : Fin 2886) := Fin.ext h1822
    subst k
    rw [keyMomentRowsAt1822]
    exact keyMoment1822 B hB
  · have he : k = (1823 : Fin 2886) := Fin.ext h1823
    subst k
    rw [keyMomentRowsAt1823]
    exact keyMoment1823 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
