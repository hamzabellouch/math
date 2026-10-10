import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound58
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1856 : keyMomentRows (1856 : Fin 2886) =
    keyMomentRow1856 := by decide +kernel

theorem keyMomentRowsAt1857 : keyMomentRows (1857 : Fin 2886) =
    keyMomentRow1857 := by decide +kernel

theorem keyMomentRowsAt1858 : keyMomentRows (1858 : Fin 2886) =
    keyMomentRow1858 := by decide +kernel

theorem keyMomentRowsAt1859 : keyMomentRows (1859 : Fin 2886) =
    keyMomentRow1859 := by decide +kernel

theorem keyMomentRowsAt1860 : keyMomentRows (1860 : Fin 2886) =
    keyMomentRow1860 := by decide +kernel

theorem keyMomentRowsAt1861 : keyMomentRows (1861 : Fin 2886) =
    keyMomentRow1861 := by decide +kernel

theorem keyMomentRowsAt1862 : keyMomentRows (1862 : Fin 2886) =
    keyMomentRow1862 := by decide +kernel

theorem keyMomentRowsAt1863 : keyMomentRows (1863 : Fin 2886) =
    keyMomentRow1863 := by decide +kernel

theorem keyMomentRowsAt1864 : keyMomentRows (1864 : Fin 2886) =
    keyMomentRow1864 := by decide +kernel

theorem keyMomentRowsAt1865 : keyMomentRows (1865 : Fin 2886) =
    keyMomentRow1865 := by decide +kernel

theorem keyMomentRowsAt1866 : keyMomentRows (1866 : Fin 2886) =
    keyMomentRow1866 := by decide +kernel

theorem keyMomentRowsAt1867 : keyMomentRows (1867 : Fin 2886) =
    keyMomentRow1867 := by decide +kernel

theorem keyMomentRowsAt1868 : keyMomentRows (1868 : Fin 2886) =
    keyMomentRow1868 := by decide +kernel

theorem keyMomentRowsAt1869 : keyMomentRows (1869 : Fin 2886) =
    keyMomentRow1869 := by decide +kernel

theorem keyMomentRowsAt1870 : keyMomentRows (1870 : Fin 2886) =
    keyMomentRow1870 := by decide +kernel

theorem keyMomentRowsAt1871 : keyMomentRows (1871 : Fin 2886) =
    keyMomentRow1871 := by decide +kernel

theorem keyMomentRowsAt1872 : keyMomentRows (1872 : Fin 2886) =
    keyMomentRow1872 := by decide +kernel

theorem keyMomentRowsAt1873 : keyMomentRows (1873 : Fin 2886) =
    keyMomentRow1873 := by decide +kernel

theorem keyMomentRowsAt1874 : keyMomentRows (1874 : Fin 2886) =
    keyMomentRow1874 := by decide +kernel

theorem keyMomentRowsAt1875 : keyMomentRows (1875 : Fin 2886) =
    keyMomentRow1875 := by decide +kernel

theorem keyMomentRowsAt1876 : keyMomentRows (1876 : Fin 2886) =
    keyMomentRow1876 := by decide +kernel

theorem keyMomentRowsAt1877 : keyMomentRows (1877 : Fin 2886) =
    keyMomentRow1877 := by decide +kernel

theorem keyMomentRowsAt1878 : keyMomentRows (1878 : Fin 2886) =
    keyMomentRow1878 := by decide +kernel

theorem keyMomentRowsAt1879 : keyMomentRows (1879 : Fin 2886) =
    keyMomentRow1879 := by decide +kernel

theorem keyMomentRowsAt1880 : keyMomentRows (1880 : Fin 2886) =
    keyMomentRow1880 := by decide +kernel

theorem keyMomentRowsAt1881 : keyMomentRows (1881 : Fin 2886) =
    keyMomentRow1881 := by decide +kernel

theorem keyMomentRowsAt1882 : keyMomentRows (1882 : Fin 2886) =
    keyMomentRow1882 := by decide +kernel

theorem keyMomentRowsAt1883 : keyMomentRows (1883 : Fin 2886) =
    keyMomentRow1883 := by decide +kernel

theorem keyMomentRowsAt1884 : keyMomentRows (1884 : Fin 2886) =
    keyMomentRow1884 := by decide +kernel

theorem keyMomentRowsAt1885 : keyMomentRows (1885 : Fin 2886) =
    keyMomentRow1885 := by decide +kernel

theorem keyMomentRowsAt1886 : keyMomentRows (1886 : Fin 2886) =
    keyMomentRow1886 := by decide +kernel

theorem keyMomentRowsAt1887 : keyMomentRows (1887 : Fin 2886) =
    keyMomentRow1887 := by decide +kernel

theorem keyMomentChunkSound58 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 58) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1856 ∨ k.val = 1857 ∨ k.val = 1858 ∨ k.val = 1859 ∨ k.val = 1860 ∨ k.val = 1861 ∨ k.val = 1862 ∨ k.val = 1863 ∨ k.val = 1864 ∨ k.val = 1865 ∨ k.val = 1866 ∨ k.val = 1867 ∨ k.val = 1868 ∨ k.val = 1869 ∨ k.val = 1870 ∨ k.val = 1871 ∨ k.val = 1872 ∨ k.val = 1873 ∨ k.val = 1874 ∨ k.val = 1875 ∨ k.val = 1876 ∨ k.val = 1877 ∨ k.val = 1878 ∨ k.val = 1879 ∨ k.val = 1880 ∨ k.val = 1881 ∨ k.val = 1882 ∨ k.val = 1883 ∨ k.val = 1884 ∨ k.val = 1885 ∨ k.val = 1886 ∨ k.val = 1887 := by omega
  rcases heq with h1856 | h1857 | h1858 | h1859 | h1860 | h1861 | h1862 | h1863 | h1864 | h1865 | h1866 | h1867 | h1868 | h1869 | h1870 | h1871 | h1872 | h1873 | h1874 | h1875 | h1876 | h1877 | h1878 | h1879 | h1880 | h1881 | h1882 | h1883 | h1884 | h1885 | h1886 | h1887
  · have he : k = (1856 : Fin 2886) := Fin.ext h1856
    subst k
    rw [keyMomentRowsAt1856]
    exact keyMoment1856 B hB
  · have he : k = (1857 : Fin 2886) := Fin.ext h1857
    subst k
    rw [keyMomentRowsAt1857]
    exact keyMoment1857 B hB
  · have he : k = (1858 : Fin 2886) := Fin.ext h1858
    subst k
    rw [keyMomentRowsAt1858]
    exact keyMoment1858 B hB
  · have he : k = (1859 : Fin 2886) := Fin.ext h1859
    subst k
    rw [keyMomentRowsAt1859]
    exact keyMoment1859 B hB
  · have he : k = (1860 : Fin 2886) := Fin.ext h1860
    subst k
    rw [keyMomentRowsAt1860]
    exact keyMoment1860 B hB
  · have he : k = (1861 : Fin 2886) := Fin.ext h1861
    subst k
    rw [keyMomentRowsAt1861]
    exact keyMoment1861 B hB
  · have he : k = (1862 : Fin 2886) := Fin.ext h1862
    subst k
    rw [keyMomentRowsAt1862]
    exact keyMoment1862 B hB
  · have he : k = (1863 : Fin 2886) := Fin.ext h1863
    subst k
    rw [keyMomentRowsAt1863]
    exact keyMoment1863 B hB
  · have he : k = (1864 : Fin 2886) := Fin.ext h1864
    subst k
    rw [keyMomentRowsAt1864]
    exact keyMoment1864 B hB
  · have he : k = (1865 : Fin 2886) := Fin.ext h1865
    subst k
    rw [keyMomentRowsAt1865]
    exact keyMoment1865 B hB
  · have he : k = (1866 : Fin 2886) := Fin.ext h1866
    subst k
    rw [keyMomentRowsAt1866]
    exact keyMoment1866 B hB
  · have he : k = (1867 : Fin 2886) := Fin.ext h1867
    subst k
    rw [keyMomentRowsAt1867]
    exact keyMoment1867 B hB
  · have he : k = (1868 : Fin 2886) := Fin.ext h1868
    subst k
    rw [keyMomentRowsAt1868]
    exact keyMoment1868 B hB
  · have he : k = (1869 : Fin 2886) := Fin.ext h1869
    subst k
    rw [keyMomentRowsAt1869]
    exact keyMoment1869 B hB
  · have he : k = (1870 : Fin 2886) := Fin.ext h1870
    subst k
    rw [keyMomentRowsAt1870]
    exact keyMoment1870 B hB
  · have he : k = (1871 : Fin 2886) := Fin.ext h1871
    subst k
    rw [keyMomentRowsAt1871]
    exact keyMoment1871 B hB
  · have he : k = (1872 : Fin 2886) := Fin.ext h1872
    subst k
    rw [keyMomentRowsAt1872]
    exact keyMoment1872 B hB
  · have he : k = (1873 : Fin 2886) := Fin.ext h1873
    subst k
    rw [keyMomentRowsAt1873]
    exact keyMoment1873 B hB
  · have he : k = (1874 : Fin 2886) := Fin.ext h1874
    subst k
    rw [keyMomentRowsAt1874]
    exact keyMoment1874 B hB
  · have he : k = (1875 : Fin 2886) := Fin.ext h1875
    subst k
    rw [keyMomentRowsAt1875]
    exact keyMoment1875 B hB
  · have he : k = (1876 : Fin 2886) := Fin.ext h1876
    subst k
    rw [keyMomentRowsAt1876]
    exact keyMoment1876 B hB
  · have he : k = (1877 : Fin 2886) := Fin.ext h1877
    subst k
    rw [keyMomentRowsAt1877]
    exact keyMoment1877 B hB
  · have he : k = (1878 : Fin 2886) := Fin.ext h1878
    subst k
    rw [keyMomentRowsAt1878]
    exact keyMoment1878 B hB
  · have he : k = (1879 : Fin 2886) := Fin.ext h1879
    subst k
    rw [keyMomentRowsAt1879]
    exact keyMoment1879 B hB
  · have he : k = (1880 : Fin 2886) := Fin.ext h1880
    subst k
    rw [keyMomentRowsAt1880]
    exact keyMoment1880 B hB
  · have he : k = (1881 : Fin 2886) := Fin.ext h1881
    subst k
    rw [keyMomentRowsAt1881]
    exact keyMoment1881 B hB
  · have he : k = (1882 : Fin 2886) := Fin.ext h1882
    subst k
    rw [keyMomentRowsAt1882]
    exact keyMoment1882 B hB
  · have he : k = (1883 : Fin 2886) := Fin.ext h1883
    subst k
    rw [keyMomentRowsAt1883]
    exact keyMoment1883 B hB
  · have he : k = (1884 : Fin 2886) := Fin.ext h1884
    subst k
    rw [keyMomentRowsAt1884]
    exact keyMoment1884 B hB
  · have he : k = (1885 : Fin 2886) := Fin.ext h1885
    subst k
    rw [keyMomentRowsAt1885]
    exact keyMoment1885 B hB
  · have he : k = (1886 : Fin 2886) := Fin.ext h1886
    subst k
    rw [keyMomentRowsAt1886]
    exact keyMoment1886 B hB
  · have he : k = (1887 : Fin 2886) := Fin.ext h1887
    subst k
    rw [keyMomentRowsAt1887]
    exact keyMoment1887 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
