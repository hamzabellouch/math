import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound59
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1888 : keyMomentRows (1888 : Fin 2886) =
    keyMomentRow1888 := by decide +kernel

theorem keyMomentRowsAt1889 : keyMomentRows (1889 : Fin 2886) =
    keyMomentRow1889 := by decide +kernel

theorem keyMomentRowsAt1890 : keyMomentRows (1890 : Fin 2886) =
    keyMomentRow1890 := by decide +kernel

theorem keyMomentRowsAt1891 : keyMomentRows (1891 : Fin 2886) =
    keyMomentRow1891 := by decide +kernel

theorem keyMomentRowsAt1892 : keyMomentRows (1892 : Fin 2886) =
    keyMomentRow1892 := by decide +kernel

theorem keyMomentRowsAt1893 : keyMomentRows (1893 : Fin 2886) =
    keyMomentRow1893 := by decide +kernel

theorem keyMomentRowsAt1894 : keyMomentRows (1894 : Fin 2886) =
    keyMomentRow1894 := by decide +kernel

theorem keyMomentRowsAt1895 : keyMomentRows (1895 : Fin 2886) =
    keyMomentRow1895 := by decide +kernel

theorem keyMomentRowsAt1896 : keyMomentRows (1896 : Fin 2886) =
    keyMomentRow1896 := by decide +kernel

theorem keyMomentRowsAt1897 : keyMomentRows (1897 : Fin 2886) =
    keyMomentRow1897 := by decide +kernel

theorem keyMomentRowsAt1898 : keyMomentRows (1898 : Fin 2886) =
    keyMomentRow1898 := by decide +kernel

theorem keyMomentRowsAt1899 : keyMomentRows (1899 : Fin 2886) =
    keyMomentRow1899 := by decide +kernel

theorem keyMomentRowsAt1900 : keyMomentRows (1900 : Fin 2886) =
    keyMomentRow1900 := by decide +kernel

theorem keyMomentRowsAt1901 : keyMomentRows (1901 : Fin 2886) =
    keyMomentRow1901 := by decide +kernel

theorem keyMomentRowsAt1902 : keyMomentRows (1902 : Fin 2886) =
    keyMomentRow1902 := by decide +kernel

theorem keyMomentRowsAt1903 : keyMomentRows (1903 : Fin 2886) =
    keyMomentRow1903 := by decide +kernel

theorem keyMomentRowsAt1904 : keyMomentRows (1904 : Fin 2886) =
    keyMomentRow1904 := by decide +kernel

theorem keyMomentRowsAt1905 : keyMomentRows (1905 : Fin 2886) =
    keyMomentRow1905 := by decide +kernel

theorem keyMomentRowsAt1906 : keyMomentRows (1906 : Fin 2886) =
    keyMomentRow1906 := by decide +kernel

theorem keyMomentRowsAt1907 : keyMomentRows (1907 : Fin 2886) =
    keyMomentRow1907 := by decide +kernel

theorem keyMomentRowsAt1908 : keyMomentRows (1908 : Fin 2886) =
    keyMomentRow1908 := by decide +kernel

theorem keyMomentRowsAt1909 : keyMomentRows (1909 : Fin 2886) =
    keyMomentRow1909 := by decide +kernel

theorem keyMomentRowsAt1910 : keyMomentRows (1910 : Fin 2886) =
    keyMomentRow1910 := by decide +kernel

theorem keyMomentRowsAt1911 : keyMomentRows (1911 : Fin 2886) =
    keyMomentRow1911 := by decide +kernel

theorem keyMomentRowsAt1912 : keyMomentRows (1912 : Fin 2886) =
    keyMomentRow1912 := by decide +kernel

theorem keyMomentRowsAt1913 : keyMomentRows (1913 : Fin 2886) =
    keyMomentRow1913 := by decide +kernel

theorem keyMomentRowsAt1914 : keyMomentRows (1914 : Fin 2886) =
    keyMomentRow1914 := by decide +kernel

theorem keyMomentRowsAt1915 : keyMomentRows (1915 : Fin 2886) =
    keyMomentRow1915 := by decide +kernel

theorem keyMomentRowsAt1916 : keyMomentRows (1916 : Fin 2886) =
    keyMomentRow1916 := by decide +kernel

theorem keyMomentRowsAt1917 : keyMomentRows (1917 : Fin 2886) =
    keyMomentRow1917 := by decide +kernel

theorem keyMomentRowsAt1918 : keyMomentRows (1918 : Fin 2886) =
    keyMomentRow1918 := by decide +kernel

theorem keyMomentRowsAt1919 : keyMomentRows (1919 : Fin 2886) =
    keyMomentRow1919 := by decide +kernel

theorem keyMomentChunkSound59 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 59) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1888 ∨ k.val = 1889 ∨ k.val = 1890 ∨ k.val = 1891 ∨ k.val = 1892 ∨ k.val = 1893 ∨ k.val = 1894 ∨ k.val = 1895 ∨ k.val = 1896 ∨ k.val = 1897 ∨ k.val = 1898 ∨ k.val = 1899 ∨ k.val = 1900 ∨ k.val = 1901 ∨ k.val = 1902 ∨ k.val = 1903 ∨ k.val = 1904 ∨ k.val = 1905 ∨ k.val = 1906 ∨ k.val = 1907 ∨ k.val = 1908 ∨ k.val = 1909 ∨ k.val = 1910 ∨ k.val = 1911 ∨ k.val = 1912 ∨ k.val = 1913 ∨ k.val = 1914 ∨ k.val = 1915 ∨ k.val = 1916 ∨ k.val = 1917 ∨ k.val = 1918 ∨ k.val = 1919 := by omega
  rcases heq with h1888 | h1889 | h1890 | h1891 | h1892 | h1893 | h1894 | h1895 | h1896 | h1897 | h1898 | h1899 | h1900 | h1901 | h1902 | h1903 | h1904 | h1905 | h1906 | h1907 | h1908 | h1909 | h1910 | h1911 | h1912 | h1913 | h1914 | h1915 | h1916 | h1917 | h1918 | h1919
  · have he : k = (1888 : Fin 2886) := Fin.ext h1888
    subst k
    rw [keyMomentRowsAt1888]
    exact keyMoment1888 B hB
  · have he : k = (1889 : Fin 2886) := Fin.ext h1889
    subst k
    rw [keyMomentRowsAt1889]
    exact keyMoment1889 B hB
  · have he : k = (1890 : Fin 2886) := Fin.ext h1890
    subst k
    rw [keyMomentRowsAt1890]
    exact keyMoment1890 B hB
  · have he : k = (1891 : Fin 2886) := Fin.ext h1891
    subst k
    rw [keyMomentRowsAt1891]
    exact keyMoment1891 B hB
  · have he : k = (1892 : Fin 2886) := Fin.ext h1892
    subst k
    rw [keyMomentRowsAt1892]
    exact keyMoment1892 B hB
  · have he : k = (1893 : Fin 2886) := Fin.ext h1893
    subst k
    rw [keyMomentRowsAt1893]
    exact keyMoment1893 B hB
  · have he : k = (1894 : Fin 2886) := Fin.ext h1894
    subst k
    rw [keyMomentRowsAt1894]
    exact keyMoment1894 B hB
  · have he : k = (1895 : Fin 2886) := Fin.ext h1895
    subst k
    rw [keyMomentRowsAt1895]
    exact keyMoment1895 B hB
  · have he : k = (1896 : Fin 2886) := Fin.ext h1896
    subst k
    rw [keyMomentRowsAt1896]
    exact keyMoment1896 B hB
  · have he : k = (1897 : Fin 2886) := Fin.ext h1897
    subst k
    rw [keyMomentRowsAt1897]
    exact keyMoment1897 B hB
  · have he : k = (1898 : Fin 2886) := Fin.ext h1898
    subst k
    rw [keyMomentRowsAt1898]
    exact keyMoment1898 B hB
  · have he : k = (1899 : Fin 2886) := Fin.ext h1899
    subst k
    rw [keyMomentRowsAt1899]
    exact keyMoment1899 B hB
  · have he : k = (1900 : Fin 2886) := Fin.ext h1900
    subst k
    rw [keyMomentRowsAt1900]
    exact keyMoment1900 B hB
  · have he : k = (1901 : Fin 2886) := Fin.ext h1901
    subst k
    rw [keyMomentRowsAt1901]
    exact keyMoment1901 B hB
  · have he : k = (1902 : Fin 2886) := Fin.ext h1902
    subst k
    rw [keyMomentRowsAt1902]
    exact keyMoment1902 B hB
  · have he : k = (1903 : Fin 2886) := Fin.ext h1903
    subst k
    rw [keyMomentRowsAt1903]
    exact keyMoment1903 B hB
  · have he : k = (1904 : Fin 2886) := Fin.ext h1904
    subst k
    rw [keyMomentRowsAt1904]
    exact keyMoment1904 B hB
  · have he : k = (1905 : Fin 2886) := Fin.ext h1905
    subst k
    rw [keyMomentRowsAt1905]
    exact keyMoment1905 B hB
  · have he : k = (1906 : Fin 2886) := Fin.ext h1906
    subst k
    rw [keyMomentRowsAt1906]
    exact keyMoment1906 B hB
  · have he : k = (1907 : Fin 2886) := Fin.ext h1907
    subst k
    rw [keyMomentRowsAt1907]
    exact keyMoment1907 B hB
  · have he : k = (1908 : Fin 2886) := Fin.ext h1908
    subst k
    rw [keyMomentRowsAt1908]
    exact keyMoment1908 B hB
  · have he : k = (1909 : Fin 2886) := Fin.ext h1909
    subst k
    rw [keyMomentRowsAt1909]
    exact keyMoment1909 B hB
  · have he : k = (1910 : Fin 2886) := Fin.ext h1910
    subst k
    rw [keyMomentRowsAt1910]
    exact keyMoment1910 B hB
  · have he : k = (1911 : Fin 2886) := Fin.ext h1911
    subst k
    rw [keyMomentRowsAt1911]
    exact keyMoment1911 B hB
  · have he : k = (1912 : Fin 2886) := Fin.ext h1912
    subst k
    rw [keyMomentRowsAt1912]
    exact keyMoment1912 B hB
  · have he : k = (1913 : Fin 2886) := Fin.ext h1913
    subst k
    rw [keyMomentRowsAt1913]
    exact keyMoment1913 B hB
  · have he : k = (1914 : Fin 2886) := Fin.ext h1914
    subst k
    rw [keyMomentRowsAt1914]
    exact keyMoment1914 B hB
  · have he : k = (1915 : Fin 2886) := Fin.ext h1915
    subst k
    rw [keyMomentRowsAt1915]
    exact keyMoment1915 B hB
  · have he : k = (1916 : Fin 2886) := Fin.ext h1916
    subst k
    rw [keyMomentRowsAt1916]
    exact keyMoment1916 B hB
  · have he : k = (1917 : Fin 2886) := Fin.ext h1917
    subst k
    rw [keyMomentRowsAt1917]
    exact keyMoment1917 B hB
  · have he : k = (1918 : Fin 2886) := Fin.ext h1918
    subst k
    rw [keyMomentRowsAt1918]
    exact keyMoment1918 B hB
  · have he : k = (1919 : Fin 2886) := Fin.ext h1919
    subst k
    rw [keyMomentRowsAt1919]
    exact keyMoment1919 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
