import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound65
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2080 : keyMomentRows (2080 : Fin 2886) =
    keyMomentRow2080 := by decide +kernel

theorem keyMomentRowsAt2081 : keyMomentRows (2081 : Fin 2886) =
    keyMomentRow2081 := by decide +kernel

theorem keyMomentRowsAt2082 : keyMomentRows (2082 : Fin 2886) =
    keyMomentRow2082 := by decide +kernel

theorem keyMomentRowsAt2083 : keyMomentRows (2083 : Fin 2886) =
    keyMomentRow2083 := by decide +kernel

theorem keyMomentRowsAt2084 : keyMomentRows (2084 : Fin 2886) =
    keyMomentRow2084 := by decide +kernel

theorem keyMomentRowsAt2085 : keyMomentRows (2085 : Fin 2886) =
    keyMomentRow2085 := by decide +kernel

theorem keyMomentRowsAt2086 : keyMomentRows (2086 : Fin 2886) =
    keyMomentRow2086 := by decide +kernel

theorem keyMomentRowsAt2087 : keyMomentRows (2087 : Fin 2886) =
    keyMomentRow2087 := by decide +kernel

theorem keyMomentRowsAt2088 : keyMomentRows (2088 : Fin 2886) =
    keyMomentRow2088 := by decide +kernel

theorem keyMomentRowsAt2089 : keyMomentRows (2089 : Fin 2886) =
    keyMomentRow2089 := by decide +kernel

theorem keyMomentRowsAt2090 : keyMomentRows (2090 : Fin 2886) =
    keyMomentRow2090 := by decide +kernel

theorem keyMomentRowsAt2091 : keyMomentRows (2091 : Fin 2886) =
    keyMomentRow2091 := by decide +kernel

theorem keyMomentRowsAt2092 : keyMomentRows (2092 : Fin 2886) =
    keyMomentRow2092 := by decide +kernel

theorem keyMomentRowsAt2093 : keyMomentRows (2093 : Fin 2886) =
    keyMomentRow2093 := by decide +kernel

theorem keyMomentRowsAt2094 : keyMomentRows (2094 : Fin 2886) =
    keyMomentRow2094 := by decide +kernel

theorem keyMomentRowsAt2095 : keyMomentRows (2095 : Fin 2886) =
    keyMomentRow2095 := by decide +kernel

theorem keyMomentRowsAt2096 : keyMomentRows (2096 : Fin 2886) =
    keyMomentRow2096 := by decide +kernel

theorem keyMomentRowsAt2097 : keyMomentRows (2097 : Fin 2886) =
    keyMomentRow2097 := by decide +kernel

theorem keyMomentRowsAt2098 : keyMomentRows (2098 : Fin 2886) =
    keyMomentRow2098 := by decide +kernel

theorem keyMomentRowsAt2099 : keyMomentRows (2099 : Fin 2886) =
    keyMomentRow2099 := by decide +kernel

theorem keyMomentRowsAt2100 : keyMomentRows (2100 : Fin 2886) =
    keyMomentRow2100 := by decide +kernel

theorem keyMomentRowsAt2101 : keyMomentRows (2101 : Fin 2886) =
    keyMomentRow2101 := by decide +kernel

theorem keyMomentRowsAt2102 : keyMomentRows (2102 : Fin 2886) =
    keyMomentRow2102 := by decide +kernel

theorem keyMomentRowsAt2103 : keyMomentRows (2103 : Fin 2886) =
    keyMomentRow2103 := by decide +kernel

theorem keyMomentRowsAt2104 : keyMomentRows (2104 : Fin 2886) =
    keyMomentRow2104 := by decide +kernel

theorem keyMomentRowsAt2105 : keyMomentRows (2105 : Fin 2886) =
    keyMomentRow2105 := by decide +kernel

theorem keyMomentRowsAt2106 : keyMomentRows (2106 : Fin 2886) =
    keyMomentRow2106 := by decide +kernel

theorem keyMomentRowsAt2107 : keyMomentRows (2107 : Fin 2886) =
    keyMomentRow2107 := by decide +kernel

theorem keyMomentRowsAt2108 : keyMomentRows (2108 : Fin 2886) =
    keyMomentRow2108 := by decide +kernel

theorem keyMomentRowsAt2109 : keyMomentRows (2109 : Fin 2886) =
    keyMomentRow2109 := by decide +kernel

theorem keyMomentRowsAt2110 : keyMomentRows (2110 : Fin 2886) =
    keyMomentRow2110 := by decide +kernel

theorem keyMomentRowsAt2111 : keyMomentRows (2111 : Fin 2886) =
    keyMomentRow2111 := by decide +kernel

theorem keyMomentChunkSound65 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 65) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2080 ∨ k.val = 2081 ∨ k.val = 2082 ∨ k.val = 2083 ∨ k.val = 2084 ∨ k.val = 2085 ∨ k.val = 2086 ∨ k.val = 2087 ∨ k.val = 2088 ∨ k.val = 2089 ∨ k.val = 2090 ∨ k.val = 2091 ∨ k.val = 2092 ∨ k.val = 2093 ∨ k.val = 2094 ∨ k.val = 2095 ∨ k.val = 2096 ∨ k.val = 2097 ∨ k.val = 2098 ∨ k.val = 2099 ∨ k.val = 2100 ∨ k.val = 2101 ∨ k.val = 2102 ∨ k.val = 2103 ∨ k.val = 2104 ∨ k.val = 2105 ∨ k.val = 2106 ∨ k.val = 2107 ∨ k.val = 2108 ∨ k.val = 2109 ∨ k.val = 2110 ∨ k.val = 2111 := by omega
  rcases heq with h2080 | h2081 | h2082 | h2083 | h2084 | h2085 | h2086 | h2087 | h2088 | h2089 | h2090 | h2091 | h2092 | h2093 | h2094 | h2095 | h2096 | h2097 | h2098 | h2099 | h2100 | h2101 | h2102 | h2103 | h2104 | h2105 | h2106 | h2107 | h2108 | h2109 | h2110 | h2111
  · have he : k = (2080 : Fin 2886) := Fin.ext h2080
    subst k
    rw [keyMomentRowsAt2080]
    exact keyMoment2080 B hB
  · have he : k = (2081 : Fin 2886) := Fin.ext h2081
    subst k
    rw [keyMomentRowsAt2081]
    exact keyMoment2081 B hB
  · have he : k = (2082 : Fin 2886) := Fin.ext h2082
    subst k
    rw [keyMomentRowsAt2082]
    exact keyMoment2082 B hB
  · have he : k = (2083 : Fin 2886) := Fin.ext h2083
    subst k
    rw [keyMomentRowsAt2083]
    exact keyMoment2083 B hB
  · have he : k = (2084 : Fin 2886) := Fin.ext h2084
    subst k
    rw [keyMomentRowsAt2084]
    exact keyMoment2084 B hB
  · have he : k = (2085 : Fin 2886) := Fin.ext h2085
    subst k
    rw [keyMomentRowsAt2085]
    exact keyMoment2085 B hB
  · have he : k = (2086 : Fin 2886) := Fin.ext h2086
    subst k
    rw [keyMomentRowsAt2086]
    exact keyMoment2086 B hB
  · have he : k = (2087 : Fin 2886) := Fin.ext h2087
    subst k
    rw [keyMomentRowsAt2087]
    exact keyMoment2087 B hB
  · have he : k = (2088 : Fin 2886) := Fin.ext h2088
    subst k
    rw [keyMomentRowsAt2088]
    exact keyMoment2088 B hB
  · have he : k = (2089 : Fin 2886) := Fin.ext h2089
    subst k
    rw [keyMomentRowsAt2089]
    exact keyMoment2089 B hB
  · have he : k = (2090 : Fin 2886) := Fin.ext h2090
    subst k
    rw [keyMomentRowsAt2090]
    exact keyMoment2090 B hB
  · have he : k = (2091 : Fin 2886) := Fin.ext h2091
    subst k
    rw [keyMomentRowsAt2091]
    exact keyMoment2091 B hB
  · have he : k = (2092 : Fin 2886) := Fin.ext h2092
    subst k
    rw [keyMomentRowsAt2092]
    exact keyMoment2092 B hB
  · have he : k = (2093 : Fin 2886) := Fin.ext h2093
    subst k
    rw [keyMomentRowsAt2093]
    exact keyMoment2093 B hB
  · have he : k = (2094 : Fin 2886) := Fin.ext h2094
    subst k
    rw [keyMomentRowsAt2094]
    exact keyMoment2094 B hB
  · have he : k = (2095 : Fin 2886) := Fin.ext h2095
    subst k
    rw [keyMomentRowsAt2095]
    exact keyMoment2095 B hB
  · have he : k = (2096 : Fin 2886) := Fin.ext h2096
    subst k
    rw [keyMomentRowsAt2096]
    exact keyMoment2096 B hB
  · have he : k = (2097 : Fin 2886) := Fin.ext h2097
    subst k
    rw [keyMomentRowsAt2097]
    exact keyMoment2097 B hB
  · have he : k = (2098 : Fin 2886) := Fin.ext h2098
    subst k
    rw [keyMomentRowsAt2098]
    exact keyMoment2098 B hB
  · have he : k = (2099 : Fin 2886) := Fin.ext h2099
    subst k
    rw [keyMomentRowsAt2099]
    exact keyMoment2099 B hB
  · have he : k = (2100 : Fin 2886) := Fin.ext h2100
    subst k
    rw [keyMomentRowsAt2100]
    exact keyMoment2100 B hB
  · have he : k = (2101 : Fin 2886) := Fin.ext h2101
    subst k
    rw [keyMomentRowsAt2101]
    exact keyMoment2101 B hB
  · have he : k = (2102 : Fin 2886) := Fin.ext h2102
    subst k
    rw [keyMomentRowsAt2102]
    exact keyMoment2102 B hB
  · have he : k = (2103 : Fin 2886) := Fin.ext h2103
    subst k
    rw [keyMomentRowsAt2103]
    exact keyMoment2103 B hB
  · have he : k = (2104 : Fin 2886) := Fin.ext h2104
    subst k
    rw [keyMomentRowsAt2104]
    exact keyMoment2104 B hB
  · have he : k = (2105 : Fin 2886) := Fin.ext h2105
    subst k
    rw [keyMomentRowsAt2105]
    exact keyMoment2105 B hB
  · have he : k = (2106 : Fin 2886) := Fin.ext h2106
    subst k
    rw [keyMomentRowsAt2106]
    exact keyMoment2106 B hB
  · have he : k = (2107 : Fin 2886) := Fin.ext h2107
    subst k
    rw [keyMomentRowsAt2107]
    exact keyMoment2107 B hB
  · have he : k = (2108 : Fin 2886) := Fin.ext h2108
    subst k
    rw [keyMomentRowsAt2108]
    exact keyMoment2108 B hB
  · have he : k = (2109 : Fin 2886) := Fin.ext h2109
    subst k
    rw [keyMomentRowsAt2109]
    exact keyMoment2109 B hB
  · have he : k = (2110 : Fin 2886) := Fin.ext h2110
    subst k
    rw [keyMomentRowsAt2110]
    exact keyMoment2110 B hB
  · have he : k = (2111 : Fin 2886) := Fin.ext h2111
    subst k
    rw [keyMomentRowsAt2111]
    exact keyMoment2111 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
