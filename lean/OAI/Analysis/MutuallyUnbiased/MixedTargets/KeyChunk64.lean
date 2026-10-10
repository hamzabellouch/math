import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound64
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2048 : keyMomentRows (2048 : Fin 2886) =
    keyMomentRow2048 := by decide +kernel

theorem keyMomentRowsAt2049 : keyMomentRows (2049 : Fin 2886) =
    keyMomentRow2049 := by decide +kernel

theorem keyMomentRowsAt2050 : keyMomentRows (2050 : Fin 2886) =
    keyMomentRow2050 := by decide +kernel

theorem keyMomentRowsAt2051 : keyMomentRows (2051 : Fin 2886) =
    keyMomentRow2051 := by decide +kernel

theorem keyMomentRowsAt2052 : keyMomentRows (2052 : Fin 2886) =
    keyMomentRow2052 := by decide +kernel

theorem keyMomentRowsAt2053 : keyMomentRows (2053 : Fin 2886) =
    keyMomentRow2053 := by decide +kernel

theorem keyMomentRowsAt2054 : keyMomentRows (2054 : Fin 2886) =
    keyMomentRow2054 := by decide +kernel

theorem keyMomentRowsAt2055 : keyMomentRows (2055 : Fin 2886) =
    keyMomentRow2055 := by decide +kernel

theorem keyMomentRowsAt2056 : keyMomentRows (2056 : Fin 2886) =
    keyMomentRow2056 := by decide +kernel

theorem keyMomentRowsAt2057 : keyMomentRows (2057 : Fin 2886) =
    keyMomentRow2057 := by decide +kernel

theorem keyMomentRowsAt2058 : keyMomentRows (2058 : Fin 2886) =
    keyMomentRow2058 := by decide +kernel

theorem keyMomentRowsAt2059 : keyMomentRows (2059 : Fin 2886) =
    keyMomentRow2059 := by decide +kernel

theorem keyMomentRowsAt2060 : keyMomentRows (2060 : Fin 2886) =
    keyMomentRow2060 := by decide +kernel

theorem keyMomentRowsAt2061 : keyMomentRows (2061 : Fin 2886) =
    keyMomentRow2061 := by decide +kernel

theorem keyMomentRowsAt2062 : keyMomentRows (2062 : Fin 2886) =
    keyMomentRow2062 := by decide +kernel

theorem keyMomentRowsAt2063 : keyMomentRows (2063 : Fin 2886) =
    keyMomentRow2063 := by decide +kernel

theorem keyMomentRowsAt2064 : keyMomentRows (2064 : Fin 2886) =
    keyMomentRow2064 := by decide +kernel

theorem keyMomentRowsAt2065 : keyMomentRows (2065 : Fin 2886) =
    keyMomentRow2065 := by decide +kernel

theorem keyMomentRowsAt2066 : keyMomentRows (2066 : Fin 2886) =
    keyMomentRow2066 := by decide +kernel

theorem keyMomentRowsAt2067 : keyMomentRows (2067 : Fin 2886) =
    keyMomentRow2067 := by decide +kernel

theorem keyMomentRowsAt2068 : keyMomentRows (2068 : Fin 2886) =
    keyMomentRow2068 := by decide +kernel

theorem keyMomentRowsAt2069 : keyMomentRows (2069 : Fin 2886) =
    keyMomentRow2069 := by decide +kernel

theorem keyMomentRowsAt2070 : keyMomentRows (2070 : Fin 2886) =
    keyMomentRow2070 := by decide +kernel

theorem keyMomentRowsAt2071 : keyMomentRows (2071 : Fin 2886) =
    keyMomentRow2071 := by decide +kernel

theorem keyMomentRowsAt2072 : keyMomentRows (2072 : Fin 2886) =
    keyMomentRow2072 := by decide +kernel

theorem keyMomentRowsAt2073 : keyMomentRows (2073 : Fin 2886) =
    keyMomentRow2073 := by decide +kernel

theorem keyMomentRowsAt2074 : keyMomentRows (2074 : Fin 2886) =
    keyMomentRow2074 := by decide +kernel

theorem keyMomentRowsAt2075 : keyMomentRows (2075 : Fin 2886) =
    keyMomentRow2075 := by decide +kernel

theorem keyMomentRowsAt2076 : keyMomentRows (2076 : Fin 2886) =
    keyMomentRow2076 := by decide +kernel

theorem keyMomentRowsAt2077 : keyMomentRows (2077 : Fin 2886) =
    keyMomentRow2077 := by decide +kernel

theorem keyMomentRowsAt2078 : keyMomentRows (2078 : Fin 2886) =
    keyMomentRow2078 := by decide +kernel

theorem keyMomentRowsAt2079 : keyMomentRows (2079 : Fin 2886) =
    keyMomentRow2079 := by decide +kernel

theorem keyMomentChunkSound64 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 64) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2048 ∨ k.val = 2049 ∨ k.val = 2050 ∨ k.val = 2051 ∨ k.val = 2052 ∨ k.val = 2053 ∨ k.val = 2054 ∨ k.val = 2055 ∨ k.val = 2056 ∨ k.val = 2057 ∨ k.val = 2058 ∨ k.val = 2059 ∨ k.val = 2060 ∨ k.val = 2061 ∨ k.val = 2062 ∨ k.val = 2063 ∨ k.val = 2064 ∨ k.val = 2065 ∨ k.val = 2066 ∨ k.val = 2067 ∨ k.val = 2068 ∨ k.val = 2069 ∨ k.val = 2070 ∨ k.val = 2071 ∨ k.val = 2072 ∨ k.val = 2073 ∨ k.val = 2074 ∨ k.val = 2075 ∨ k.val = 2076 ∨ k.val = 2077 ∨ k.val = 2078 ∨ k.val = 2079 := by omega
  rcases heq with h2048 | h2049 | h2050 | h2051 | h2052 | h2053 | h2054 | h2055 | h2056 | h2057 | h2058 | h2059 | h2060 | h2061 | h2062 | h2063 | h2064 | h2065 | h2066 | h2067 | h2068 | h2069 | h2070 | h2071 | h2072 | h2073 | h2074 | h2075 | h2076 | h2077 | h2078 | h2079
  · have he : k = (2048 : Fin 2886) := Fin.ext h2048
    subst k
    rw [keyMomentRowsAt2048]
    exact keyMoment2048 B hB
  · have he : k = (2049 : Fin 2886) := Fin.ext h2049
    subst k
    rw [keyMomentRowsAt2049]
    exact keyMoment2049 B hB
  · have he : k = (2050 : Fin 2886) := Fin.ext h2050
    subst k
    rw [keyMomentRowsAt2050]
    exact keyMoment2050 B hB
  · have he : k = (2051 : Fin 2886) := Fin.ext h2051
    subst k
    rw [keyMomentRowsAt2051]
    exact keyMoment2051 B hB
  · have he : k = (2052 : Fin 2886) := Fin.ext h2052
    subst k
    rw [keyMomentRowsAt2052]
    exact keyMoment2052 B hB
  · have he : k = (2053 : Fin 2886) := Fin.ext h2053
    subst k
    rw [keyMomentRowsAt2053]
    exact keyMoment2053 B hB
  · have he : k = (2054 : Fin 2886) := Fin.ext h2054
    subst k
    rw [keyMomentRowsAt2054]
    exact keyMoment2054 B hB
  · have he : k = (2055 : Fin 2886) := Fin.ext h2055
    subst k
    rw [keyMomentRowsAt2055]
    exact keyMoment2055 B hB
  · have he : k = (2056 : Fin 2886) := Fin.ext h2056
    subst k
    rw [keyMomentRowsAt2056]
    exact keyMoment2056 B hB
  · have he : k = (2057 : Fin 2886) := Fin.ext h2057
    subst k
    rw [keyMomentRowsAt2057]
    exact keyMoment2057 B hB
  · have he : k = (2058 : Fin 2886) := Fin.ext h2058
    subst k
    rw [keyMomentRowsAt2058]
    exact keyMoment2058 B hB
  · have he : k = (2059 : Fin 2886) := Fin.ext h2059
    subst k
    rw [keyMomentRowsAt2059]
    exact keyMoment2059 B hB
  · have he : k = (2060 : Fin 2886) := Fin.ext h2060
    subst k
    rw [keyMomentRowsAt2060]
    exact keyMoment2060 B hB
  · have he : k = (2061 : Fin 2886) := Fin.ext h2061
    subst k
    rw [keyMomentRowsAt2061]
    exact keyMoment2061 B hB
  · have he : k = (2062 : Fin 2886) := Fin.ext h2062
    subst k
    rw [keyMomentRowsAt2062]
    exact keyMoment2062 B hB
  · have he : k = (2063 : Fin 2886) := Fin.ext h2063
    subst k
    rw [keyMomentRowsAt2063]
    exact keyMoment2063 B hB
  · have he : k = (2064 : Fin 2886) := Fin.ext h2064
    subst k
    rw [keyMomentRowsAt2064]
    exact keyMoment2064 B hB
  · have he : k = (2065 : Fin 2886) := Fin.ext h2065
    subst k
    rw [keyMomentRowsAt2065]
    exact keyMoment2065 B hB
  · have he : k = (2066 : Fin 2886) := Fin.ext h2066
    subst k
    rw [keyMomentRowsAt2066]
    exact keyMoment2066 B hB
  · have he : k = (2067 : Fin 2886) := Fin.ext h2067
    subst k
    rw [keyMomentRowsAt2067]
    exact keyMoment2067 B hB
  · have he : k = (2068 : Fin 2886) := Fin.ext h2068
    subst k
    rw [keyMomentRowsAt2068]
    exact keyMoment2068 B hB
  · have he : k = (2069 : Fin 2886) := Fin.ext h2069
    subst k
    rw [keyMomentRowsAt2069]
    exact keyMoment2069 B hB
  · have he : k = (2070 : Fin 2886) := Fin.ext h2070
    subst k
    rw [keyMomentRowsAt2070]
    exact keyMoment2070 B hB
  · have he : k = (2071 : Fin 2886) := Fin.ext h2071
    subst k
    rw [keyMomentRowsAt2071]
    exact keyMoment2071 B hB
  · have he : k = (2072 : Fin 2886) := Fin.ext h2072
    subst k
    rw [keyMomentRowsAt2072]
    exact keyMoment2072 B hB
  · have he : k = (2073 : Fin 2886) := Fin.ext h2073
    subst k
    rw [keyMomentRowsAt2073]
    exact keyMoment2073 B hB
  · have he : k = (2074 : Fin 2886) := Fin.ext h2074
    subst k
    rw [keyMomentRowsAt2074]
    exact keyMoment2074 B hB
  · have he : k = (2075 : Fin 2886) := Fin.ext h2075
    subst k
    rw [keyMomentRowsAt2075]
    exact keyMoment2075 B hB
  · have he : k = (2076 : Fin 2886) := Fin.ext h2076
    subst k
    rw [keyMomentRowsAt2076]
    exact keyMoment2076 B hB
  · have he : k = (2077 : Fin 2886) := Fin.ext h2077
    subst k
    rw [keyMomentRowsAt2077]
    exact keyMoment2077 B hB
  · have he : k = (2078 : Fin 2886) := Fin.ext h2078
    subst k
    rw [keyMomentRowsAt2078]
    exact keyMoment2078 B hB
  · have he : k = (2079 : Fin 2886) := Fin.ext h2079
    subst k
    rw [keyMomentRowsAt2079]
    exact keyMoment2079 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
