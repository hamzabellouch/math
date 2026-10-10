import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound57
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1824 : keyMomentRows (1824 : Fin 2886) =
    keyMomentRow1824 := by decide +kernel

theorem keyMomentRowsAt1825 : keyMomentRows (1825 : Fin 2886) =
    keyMomentRow1825 := by decide +kernel

theorem keyMomentRowsAt1826 : keyMomentRows (1826 : Fin 2886) =
    keyMomentRow1826 := by decide +kernel

theorem keyMomentRowsAt1827 : keyMomentRows (1827 : Fin 2886) =
    keyMomentRow1827 := by decide +kernel

theorem keyMomentRowsAt1828 : keyMomentRows (1828 : Fin 2886) =
    keyMomentRow1828 := by decide +kernel

theorem keyMomentRowsAt1829 : keyMomentRows (1829 : Fin 2886) =
    keyMomentRow1829 := by decide +kernel

theorem keyMomentRowsAt1830 : keyMomentRows (1830 : Fin 2886) =
    keyMomentRow1830 := by decide +kernel

theorem keyMomentRowsAt1831 : keyMomentRows (1831 : Fin 2886) =
    keyMomentRow1831 := by decide +kernel

theorem keyMomentRowsAt1832 : keyMomentRows (1832 : Fin 2886) =
    keyMomentRow1832 := by decide +kernel

theorem keyMomentRowsAt1833 : keyMomentRows (1833 : Fin 2886) =
    keyMomentRow1833 := by decide +kernel

theorem keyMomentRowsAt1834 : keyMomentRows (1834 : Fin 2886) =
    keyMomentRow1834 := by decide +kernel

theorem keyMomentRowsAt1835 : keyMomentRows (1835 : Fin 2886) =
    keyMomentRow1835 := by decide +kernel

theorem keyMomentRowsAt1836 : keyMomentRows (1836 : Fin 2886) =
    keyMomentRow1836 := by decide +kernel

theorem keyMomentRowsAt1837 : keyMomentRows (1837 : Fin 2886) =
    keyMomentRow1837 := by decide +kernel

theorem keyMomentRowsAt1838 : keyMomentRows (1838 : Fin 2886) =
    keyMomentRow1838 := by decide +kernel

theorem keyMomentRowsAt1839 : keyMomentRows (1839 : Fin 2886) =
    keyMomentRow1839 := by decide +kernel

theorem keyMomentRowsAt1840 : keyMomentRows (1840 : Fin 2886) =
    keyMomentRow1840 := by decide +kernel

theorem keyMomentRowsAt1841 : keyMomentRows (1841 : Fin 2886) =
    keyMomentRow1841 := by decide +kernel

theorem keyMomentRowsAt1842 : keyMomentRows (1842 : Fin 2886) =
    keyMomentRow1842 := by decide +kernel

theorem keyMomentRowsAt1843 : keyMomentRows (1843 : Fin 2886) =
    keyMomentRow1843 := by decide +kernel

theorem keyMomentRowsAt1844 : keyMomentRows (1844 : Fin 2886) =
    keyMomentRow1844 := by decide +kernel

theorem keyMomentRowsAt1845 : keyMomentRows (1845 : Fin 2886) =
    keyMomentRow1845 := by decide +kernel

theorem keyMomentRowsAt1846 : keyMomentRows (1846 : Fin 2886) =
    keyMomentRow1846 := by decide +kernel

theorem keyMomentRowsAt1847 : keyMomentRows (1847 : Fin 2886) =
    keyMomentRow1847 := by decide +kernel

theorem keyMomentRowsAt1848 : keyMomentRows (1848 : Fin 2886) =
    keyMomentRow1848 := by decide +kernel

theorem keyMomentRowsAt1849 : keyMomentRows (1849 : Fin 2886) =
    keyMomentRow1849 := by decide +kernel

theorem keyMomentRowsAt1850 : keyMomentRows (1850 : Fin 2886) =
    keyMomentRow1850 := by decide +kernel

theorem keyMomentRowsAt1851 : keyMomentRows (1851 : Fin 2886) =
    keyMomentRow1851 := by decide +kernel

theorem keyMomentRowsAt1852 : keyMomentRows (1852 : Fin 2886) =
    keyMomentRow1852 := by decide +kernel

theorem keyMomentRowsAt1853 : keyMomentRows (1853 : Fin 2886) =
    keyMomentRow1853 := by decide +kernel

theorem keyMomentRowsAt1854 : keyMomentRows (1854 : Fin 2886) =
    keyMomentRow1854 := by decide +kernel

theorem keyMomentRowsAt1855 : keyMomentRows (1855 : Fin 2886) =
    keyMomentRow1855 := by decide +kernel

theorem keyMomentChunkSound57 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 57) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1824 ∨ k.val = 1825 ∨ k.val = 1826 ∨ k.val = 1827 ∨ k.val = 1828 ∨ k.val = 1829 ∨ k.val = 1830 ∨ k.val = 1831 ∨ k.val = 1832 ∨ k.val = 1833 ∨ k.val = 1834 ∨ k.val = 1835 ∨ k.val = 1836 ∨ k.val = 1837 ∨ k.val = 1838 ∨ k.val = 1839 ∨ k.val = 1840 ∨ k.val = 1841 ∨ k.val = 1842 ∨ k.val = 1843 ∨ k.val = 1844 ∨ k.val = 1845 ∨ k.val = 1846 ∨ k.val = 1847 ∨ k.val = 1848 ∨ k.val = 1849 ∨ k.val = 1850 ∨ k.val = 1851 ∨ k.val = 1852 ∨ k.val = 1853 ∨ k.val = 1854 ∨ k.val = 1855 := by omega
  rcases heq with h1824 | h1825 | h1826 | h1827 | h1828 | h1829 | h1830 | h1831 | h1832 | h1833 | h1834 | h1835 | h1836 | h1837 | h1838 | h1839 | h1840 | h1841 | h1842 | h1843 | h1844 | h1845 | h1846 | h1847 | h1848 | h1849 | h1850 | h1851 | h1852 | h1853 | h1854 | h1855
  · have he : k = (1824 : Fin 2886) := Fin.ext h1824
    subst k
    rw [keyMomentRowsAt1824]
    exact keyMoment1824 B hB
  · have he : k = (1825 : Fin 2886) := Fin.ext h1825
    subst k
    rw [keyMomentRowsAt1825]
    exact keyMoment1825 B hB
  · have he : k = (1826 : Fin 2886) := Fin.ext h1826
    subst k
    rw [keyMomentRowsAt1826]
    exact keyMoment1826 B hB
  · have he : k = (1827 : Fin 2886) := Fin.ext h1827
    subst k
    rw [keyMomentRowsAt1827]
    exact keyMoment1827 B hB
  · have he : k = (1828 : Fin 2886) := Fin.ext h1828
    subst k
    rw [keyMomentRowsAt1828]
    exact keyMoment1828 B hB
  · have he : k = (1829 : Fin 2886) := Fin.ext h1829
    subst k
    rw [keyMomentRowsAt1829]
    exact keyMoment1829 B hB
  · have he : k = (1830 : Fin 2886) := Fin.ext h1830
    subst k
    rw [keyMomentRowsAt1830]
    exact keyMoment1830 B hB
  · have he : k = (1831 : Fin 2886) := Fin.ext h1831
    subst k
    rw [keyMomentRowsAt1831]
    exact keyMoment1831 B hB
  · have he : k = (1832 : Fin 2886) := Fin.ext h1832
    subst k
    rw [keyMomentRowsAt1832]
    exact keyMoment1832 B hB
  · have he : k = (1833 : Fin 2886) := Fin.ext h1833
    subst k
    rw [keyMomentRowsAt1833]
    exact keyMoment1833 B hB
  · have he : k = (1834 : Fin 2886) := Fin.ext h1834
    subst k
    rw [keyMomentRowsAt1834]
    exact keyMoment1834 B hB
  · have he : k = (1835 : Fin 2886) := Fin.ext h1835
    subst k
    rw [keyMomentRowsAt1835]
    exact keyMoment1835 B hB
  · have he : k = (1836 : Fin 2886) := Fin.ext h1836
    subst k
    rw [keyMomentRowsAt1836]
    exact keyMoment1836 B hB
  · have he : k = (1837 : Fin 2886) := Fin.ext h1837
    subst k
    rw [keyMomentRowsAt1837]
    exact keyMoment1837 B hB
  · have he : k = (1838 : Fin 2886) := Fin.ext h1838
    subst k
    rw [keyMomentRowsAt1838]
    exact keyMoment1838 B hB
  · have he : k = (1839 : Fin 2886) := Fin.ext h1839
    subst k
    rw [keyMomentRowsAt1839]
    exact keyMoment1839 B hB
  · have he : k = (1840 : Fin 2886) := Fin.ext h1840
    subst k
    rw [keyMomentRowsAt1840]
    exact keyMoment1840 B hB
  · have he : k = (1841 : Fin 2886) := Fin.ext h1841
    subst k
    rw [keyMomentRowsAt1841]
    exact keyMoment1841 B hB
  · have he : k = (1842 : Fin 2886) := Fin.ext h1842
    subst k
    rw [keyMomentRowsAt1842]
    exact keyMoment1842 B hB
  · have he : k = (1843 : Fin 2886) := Fin.ext h1843
    subst k
    rw [keyMomentRowsAt1843]
    exact keyMoment1843 B hB
  · have he : k = (1844 : Fin 2886) := Fin.ext h1844
    subst k
    rw [keyMomentRowsAt1844]
    exact keyMoment1844 B hB
  · have he : k = (1845 : Fin 2886) := Fin.ext h1845
    subst k
    rw [keyMomentRowsAt1845]
    exact keyMoment1845 B hB
  · have he : k = (1846 : Fin 2886) := Fin.ext h1846
    subst k
    rw [keyMomentRowsAt1846]
    exact keyMoment1846 B hB
  · have he : k = (1847 : Fin 2886) := Fin.ext h1847
    subst k
    rw [keyMomentRowsAt1847]
    exact keyMoment1847 B hB
  · have he : k = (1848 : Fin 2886) := Fin.ext h1848
    subst k
    rw [keyMomentRowsAt1848]
    exact keyMoment1848 B hB
  · have he : k = (1849 : Fin 2886) := Fin.ext h1849
    subst k
    rw [keyMomentRowsAt1849]
    exact keyMoment1849 B hB
  · have he : k = (1850 : Fin 2886) := Fin.ext h1850
    subst k
    rw [keyMomentRowsAt1850]
    exact keyMoment1850 B hB
  · have he : k = (1851 : Fin 2886) := Fin.ext h1851
    subst k
    rw [keyMomentRowsAt1851]
    exact keyMoment1851 B hB
  · have he : k = (1852 : Fin 2886) := Fin.ext h1852
    subst k
    rw [keyMomentRowsAt1852]
    exact keyMoment1852 B hB
  · have he : k = (1853 : Fin 2886) := Fin.ext h1853
    subst k
    rw [keyMomentRowsAt1853]
    exact keyMoment1853 B hB
  · have he : k = (1854 : Fin 2886) := Fin.ext h1854
    subst k
    rw [keyMomentRowsAt1854]
    exact keyMoment1854 B hB
  · have he : k = (1855 : Fin 2886) := Fin.ext h1855
    subst k
    rw [keyMomentRowsAt1855]
    exact keyMoment1855 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
