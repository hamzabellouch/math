import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound60
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1920 : keyMomentRows (1920 : Fin 2886) =
    keyMomentRow1920 := by decide +kernel

theorem keyMomentRowsAt1921 : keyMomentRows (1921 : Fin 2886) =
    keyMomentRow1921 := by decide +kernel

theorem keyMomentRowsAt1922 : keyMomentRows (1922 : Fin 2886) =
    keyMomentRow1922 := by decide +kernel

theorem keyMomentRowsAt1923 : keyMomentRows (1923 : Fin 2886) =
    keyMomentRow1923 := by decide +kernel

theorem keyMomentRowsAt1924 : keyMomentRows (1924 : Fin 2886) =
    keyMomentRow1924 := by decide +kernel

theorem keyMomentRowsAt1925 : keyMomentRows (1925 : Fin 2886) =
    keyMomentRow1925 := by decide +kernel

theorem keyMomentRowsAt1926 : keyMomentRows (1926 : Fin 2886) =
    keyMomentRow1926 := by decide +kernel

theorem keyMomentRowsAt1927 : keyMomentRows (1927 : Fin 2886) =
    keyMomentRow1927 := by decide +kernel

theorem keyMomentRowsAt1928 : keyMomentRows (1928 : Fin 2886) =
    keyMomentRow1928 := by decide +kernel

theorem keyMomentRowsAt1929 : keyMomentRows (1929 : Fin 2886) =
    keyMomentRow1929 := by decide +kernel

theorem keyMomentRowsAt1930 : keyMomentRows (1930 : Fin 2886) =
    keyMomentRow1930 := by decide +kernel

theorem keyMomentRowsAt1931 : keyMomentRows (1931 : Fin 2886) =
    keyMomentRow1931 := by decide +kernel

theorem keyMomentRowsAt1932 : keyMomentRows (1932 : Fin 2886) =
    keyMomentRow1932 := by decide +kernel

theorem keyMomentRowsAt1933 : keyMomentRows (1933 : Fin 2886) =
    keyMomentRow1933 := by decide +kernel

theorem keyMomentRowsAt1934 : keyMomentRows (1934 : Fin 2886) =
    keyMomentRow1934 := by decide +kernel

theorem keyMomentRowsAt1935 : keyMomentRows (1935 : Fin 2886) =
    keyMomentRow1935 := by decide +kernel

theorem keyMomentRowsAt1936 : keyMomentRows (1936 : Fin 2886) =
    keyMomentRow1936 := by decide +kernel

theorem keyMomentRowsAt1937 : keyMomentRows (1937 : Fin 2886) =
    keyMomentRow1937 := by decide +kernel

theorem keyMomentRowsAt1938 : keyMomentRows (1938 : Fin 2886) =
    keyMomentRow1938 := by decide +kernel

theorem keyMomentRowsAt1939 : keyMomentRows (1939 : Fin 2886) =
    keyMomentRow1939 := by decide +kernel

theorem keyMomentRowsAt1940 : keyMomentRows (1940 : Fin 2886) =
    keyMomentRow1940 := by decide +kernel

theorem keyMomentRowsAt1941 : keyMomentRows (1941 : Fin 2886) =
    keyMomentRow1941 := by decide +kernel

theorem keyMomentRowsAt1942 : keyMomentRows (1942 : Fin 2886) =
    keyMomentRow1942 := by decide +kernel

theorem keyMomentRowsAt1943 : keyMomentRows (1943 : Fin 2886) =
    keyMomentRow1943 := by decide +kernel

theorem keyMomentRowsAt1944 : keyMomentRows (1944 : Fin 2886) =
    keyMomentRow1944 := by decide +kernel

theorem keyMomentRowsAt1945 : keyMomentRows (1945 : Fin 2886) =
    keyMomentRow1945 := by decide +kernel

theorem keyMomentRowsAt1946 : keyMomentRows (1946 : Fin 2886) =
    keyMomentRow1946 := by decide +kernel

theorem keyMomentRowsAt1947 : keyMomentRows (1947 : Fin 2886) =
    keyMomentRow1947 := by decide +kernel

theorem keyMomentRowsAt1948 : keyMomentRows (1948 : Fin 2886) =
    keyMomentRow1948 := by decide +kernel

theorem keyMomentRowsAt1949 : keyMomentRows (1949 : Fin 2886) =
    keyMomentRow1949 := by decide +kernel

theorem keyMomentRowsAt1950 : keyMomentRows (1950 : Fin 2886) =
    keyMomentRow1950 := by decide +kernel

theorem keyMomentRowsAt1951 : keyMomentRows (1951 : Fin 2886) =
    keyMomentRow1951 := by decide +kernel

theorem keyMomentChunkSound60 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 60) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1920 ∨ k.val = 1921 ∨ k.val = 1922 ∨ k.val = 1923 ∨ k.val = 1924 ∨ k.val = 1925 ∨ k.val = 1926 ∨ k.val = 1927 ∨ k.val = 1928 ∨ k.val = 1929 ∨ k.val = 1930 ∨ k.val = 1931 ∨ k.val = 1932 ∨ k.val = 1933 ∨ k.val = 1934 ∨ k.val = 1935 ∨ k.val = 1936 ∨ k.val = 1937 ∨ k.val = 1938 ∨ k.val = 1939 ∨ k.val = 1940 ∨ k.val = 1941 ∨ k.val = 1942 ∨ k.val = 1943 ∨ k.val = 1944 ∨ k.val = 1945 ∨ k.val = 1946 ∨ k.val = 1947 ∨ k.val = 1948 ∨ k.val = 1949 ∨ k.val = 1950 ∨ k.val = 1951 := by omega
  rcases heq with h1920 | h1921 | h1922 | h1923 | h1924 | h1925 | h1926 | h1927 | h1928 | h1929 | h1930 | h1931 | h1932 | h1933 | h1934 | h1935 | h1936 | h1937 | h1938 | h1939 | h1940 | h1941 | h1942 | h1943 | h1944 | h1945 | h1946 | h1947 | h1948 | h1949 | h1950 | h1951
  · have he : k = (1920 : Fin 2886) := Fin.ext h1920
    subst k
    rw [keyMomentRowsAt1920]
    exact keyMoment1920 B hB
  · have he : k = (1921 : Fin 2886) := Fin.ext h1921
    subst k
    rw [keyMomentRowsAt1921]
    exact keyMoment1921 B hB
  · have he : k = (1922 : Fin 2886) := Fin.ext h1922
    subst k
    rw [keyMomentRowsAt1922]
    exact keyMoment1922 B hB
  · have he : k = (1923 : Fin 2886) := Fin.ext h1923
    subst k
    rw [keyMomentRowsAt1923]
    exact keyMoment1923 B hB
  · have he : k = (1924 : Fin 2886) := Fin.ext h1924
    subst k
    rw [keyMomentRowsAt1924]
    exact keyMoment1924 B hB
  · have he : k = (1925 : Fin 2886) := Fin.ext h1925
    subst k
    rw [keyMomentRowsAt1925]
    exact keyMoment1925 B hB
  · have he : k = (1926 : Fin 2886) := Fin.ext h1926
    subst k
    rw [keyMomentRowsAt1926]
    exact keyMoment1926 B hB
  · have he : k = (1927 : Fin 2886) := Fin.ext h1927
    subst k
    rw [keyMomentRowsAt1927]
    exact keyMoment1927 B hB
  · have he : k = (1928 : Fin 2886) := Fin.ext h1928
    subst k
    rw [keyMomentRowsAt1928]
    exact keyMoment1928 B hB
  · have he : k = (1929 : Fin 2886) := Fin.ext h1929
    subst k
    rw [keyMomentRowsAt1929]
    exact keyMoment1929 B hB
  · have he : k = (1930 : Fin 2886) := Fin.ext h1930
    subst k
    rw [keyMomentRowsAt1930]
    exact keyMoment1930 B hB
  · have he : k = (1931 : Fin 2886) := Fin.ext h1931
    subst k
    rw [keyMomentRowsAt1931]
    exact keyMoment1931 B hB
  · have he : k = (1932 : Fin 2886) := Fin.ext h1932
    subst k
    rw [keyMomentRowsAt1932]
    exact keyMoment1932 B hB
  · have he : k = (1933 : Fin 2886) := Fin.ext h1933
    subst k
    rw [keyMomentRowsAt1933]
    exact keyMoment1933 B hB
  · have he : k = (1934 : Fin 2886) := Fin.ext h1934
    subst k
    rw [keyMomentRowsAt1934]
    exact keyMoment1934 B hB
  · have he : k = (1935 : Fin 2886) := Fin.ext h1935
    subst k
    rw [keyMomentRowsAt1935]
    exact keyMoment1935 B hB
  · have he : k = (1936 : Fin 2886) := Fin.ext h1936
    subst k
    rw [keyMomentRowsAt1936]
    exact keyMoment1936 B hB
  · have he : k = (1937 : Fin 2886) := Fin.ext h1937
    subst k
    rw [keyMomentRowsAt1937]
    exact keyMoment1937 B hB
  · have he : k = (1938 : Fin 2886) := Fin.ext h1938
    subst k
    rw [keyMomentRowsAt1938]
    exact keyMoment1938 B hB
  · have he : k = (1939 : Fin 2886) := Fin.ext h1939
    subst k
    rw [keyMomentRowsAt1939]
    exact keyMoment1939 B hB
  · have he : k = (1940 : Fin 2886) := Fin.ext h1940
    subst k
    rw [keyMomentRowsAt1940]
    exact keyMoment1940 B hB
  · have he : k = (1941 : Fin 2886) := Fin.ext h1941
    subst k
    rw [keyMomentRowsAt1941]
    exact keyMoment1941 B hB
  · have he : k = (1942 : Fin 2886) := Fin.ext h1942
    subst k
    rw [keyMomentRowsAt1942]
    exact keyMoment1942 B hB
  · have he : k = (1943 : Fin 2886) := Fin.ext h1943
    subst k
    rw [keyMomentRowsAt1943]
    exact keyMoment1943 B hB
  · have he : k = (1944 : Fin 2886) := Fin.ext h1944
    subst k
    rw [keyMomentRowsAt1944]
    exact keyMoment1944 B hB
  · have he : k = (1945 : Fin 2886) := Fin.ext h1945
    subst k
    rw [keyMomentRowsAt1945]
    exact keyMoment1945 B hB
  · have he : k = (1946 : Fin 2886) := Fin.ext h1946
    subst k
    rw [keyMomentRowsAt1946]
    exact keyMoment1946 B hB
  · have he : k = (1947 : Fin 2886) := Fin.ext h1947
    subst k
    rw [keyMomentRowsAt1947]
    exact keyMoment1947 B hB
  · have he : k = (1948 : Fin 2886) := Fin.ext h1948
    subst k
    rw [keyMomentRowsAt1948]
    exact keyMoment1948 B hB
  · have he : k = (1949 : Fin 2886) := Fin.ext h1949
    subst k
    rw [keyMomentRowsAt1949]
    exact keyMoment1949 B hB
  · have he : k = (1950 : Fin 2886) := Fin.ext h1950
    subst k
    rw [keyMomentRowsAt1950]
    exact keyMoment1950 B hB
  · have he : k = (1951 : Fin 2886) := Fin.ext h1951
    subst k
    rw [keyMomentRowsAt1951]
    exact keyMoment1951 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
