import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound66
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2112 : keyMomentRows (2112 : Fin 2886) =
    keyMomentRow2112 := by decide +kernel

theorem keyMomentRowsAt2113 : keyMomentRows (2113 : Fin 2886) =
    keyMomentRow2113 := by decide +kernel

theorem keyMomentRowsAt2114 : keyMomentRows (2114 : Fin 2886) =
    keyMomentRow2114 := by decide +kernel

theorem keyMomentRowsAt2115 : keyMomentRows (2115 : Fin 2886) =
    keyMomentRow2115 := by decide +kernel

theorem keyMomentRowsAt2116 : keyMomentRows (2116 : Fin 2886) =
    keyMomentRow2116 := by decide +kernel

theorem keyMomentRowsAt2117 : keyMomentRows (2117 : Fin 2886) =
    keyMomentRow2117 := by decide +kernel

theorem keyMomentRowsAt2118 : keyMomentRows (2118 : Fin 2886) =
    keyMomentRow2118 := by decide +kernel

theorem keyMomentRowsAt2119 : keyMomentRows (2119 : Fin 2886) =
    keyMomentRow2119 := by decide +kernel

theorem keyMomentRowsAt2120 : keyMomentRows (2120 : Fin 2886) =
    keyMomentRow2120 := by decide +kernel

theorem keyMomentRowsAt2121 : keyMomentRows (2121 : Fin 2886) =
    keyMomentRow2121 := by decide +kernel

theorem keyMomentRowsAt2122 : keyMomentRows (2122 : Fin 2886) =
    keyMomentRow2122 := by decide +kernel

theorem keyMomentRowsAt2123 : keyMomentRows (2123 : Fin 2886) =
    keyMomentRow2123 := by decide +kernel

theorem keyMomentRowsAt2124 : keyMomentRows (2124 : Fin 2886) =
    keyMomentRow2124 := by decide +kernel

theorem keyMomentRowsAt2125 : keyMomentRows (2125 : Fin 2886) =
    keyMomentRow2125 := by decide +kernel

theorem keyMomentRowsAt2126 : keyMomentRows (2126 : Fin 2886) =
    keyMomentRow2126 := by decide +kernel

theorem keyMomentRowsAt2127 : keyMomentRows (2127 : Fin 2886) =
    keyMomentRow2127 := by decide +kernel

theorem keyMomentRowsAt2128 : keyMomentRows (2128 : Fin 2886) =
    keyMomentRow2128 := by decide +kernel

theorem keyMomentRowsAt2129 : keyMomentRows (2129 : Fin 2886) =
    keyMomentRow2129 := by decide +kernel

theorem keyMomentRowsAt2130 : keyMomentRows (2130 : Fin 2886) =
    keyMomentRow2130 := by decide +kernel

theorem keyMomentRowsAt2131 : keyMomentRows (2131 : Fin 2886) =
    keyMomentRow2131 := by decide +kernel

theorem keyMomentRowsAt2132 : keyMomentRows (2132 : Fin 2886) =
    keyMomentRow2132 := by decide +kernel

theorem keyMomentRowsAt2133 : keyMomentRows (2133 : Fin 2886) =
    keyMomentRow2133 := by decide +kernel

theorem keyMomentRowsAt2134 : keyMomentRows (2134 : Fin 2886) =
    keyMomentRow2134 := by decide +kernel

theorem keyMomentRowsAt2135 : keyMomentRows (2135 : Fin 2886) =
    keyMomentRow2135 := by decide +kernel

theorem keyMomentRowsAt2136 : keyMomentRows (2136 : Fin 2886) =
    keyMomentRow2136 := by decide +kernel

theorem keyMomentRowsAt2137 : keyMomentRows (2137 : Fin 2886) =
    keyMomentRow2137 := by decide +kernel

theorem keyMomentRowsAt2138 : keyMomentRows (2138 : Fin 2886) =
    keyMomentRow2138 := by decide +kernel

theorem keyMomentRowsAt2139 : keyMomentRows (2139 : Fin 2886) =
    keyMomentRow2139 := by decide +kernel

theorem keyMomentRowsAt2140 : keyMomentRows (2140 : Fin 2886) =
    keyMomentRow2140 := by decide +kernel

theorem keyMomentRowsAt2141 : keyMomentRows (2141 : Fin 2886) =
    keyMomentRow2141 := by decide +kernel

theorem keyMomentRowsAt2142 : keyMomentRows (2142 : Fin 2886) =
    keyMomentRow2142 := by decide +kernel

theorem keyMomentRowsAt2143 : keyMomentRows (2143 : Fin 2886) =
    keyMomentRow2143 := by decide +kernel

theorem keyMomentChunkSound66 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 66) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2112 ∨ k.val = 2113 ∨ k.val = 2114 ∨ k.val = 2115 ∨ k.val = 2116 ∨ k.val = 2117 ∨ k.val = 2118 ∨ k.val = 2119 ∨ k.val = 2120 ∨ k.val = 2121 ∨ k.val = 2122 ∨ k.val = 2123 ∨ k.val = 2124 ∨ k.val = 2125 ∨ k.val = 2126 ∨ k.val = 2127 ∨ k.val = 2128 ∨ k.val = 2129 ∨ k.val = 2130 ∨ k.val = 2131 ∨ k.val = 2132 ∨ k.val = 2133 ∨ k.val = 2134 ∨ k.val = 2135 ∨ k.val = 2136 ∨ k.val = 2137 ∨ k.val = 2138 ∨ k.val = 2139 ∨ k.val = 2140 ∨ k.val = 2141 ∨ k.val = 2142 ∨ k.val = 2143 := by omega
  rcases heq with h2112 | h2113 | h2114 | h2115 | h2116 | h2117 | h2118 | h2119 | h2120 | h2121 | h2122 | h2123 | h2124 | h2125 | h2126 | h2127 | h2128 | h2129 | h2130 | h2131 | h2132 | h2133 | h2134 | h2135 | h2136 | h2137 | h2138 | h2139 | h2140 | h2141 | h2142 | h2143
  · have he : k = (2112 : Fin 2886) := Fin.ext h2112
    subst k
    rw [keyMomentRowsAt2112]
    exact keyMoment2112 B hB
  · have he : k = (2113 : Fin 2886) := Fin.ext h2113
    subst k
    rw [keyMomentRowsAt2113]
    exact keyMoment2113 B hB
  · have he : k = (2114 : Fin 2886) := Fin.ext h2114
    subst k
    rw [keyMomentRowsAt2114]
    exact keyMoment2114 B hB
  · have he : k = (2115 : Fin 2886) := Fin.ext h2115
    subst k
    rw [keyMomentRowsAt2115]
    exact keyMoment2115 B hB
  · have he : k = (2116 : Fin 2886) := Fin.ext h2116
    subst k
    rw [keyMomentRowsAt2116]
    exact keyMoment2116 B hB
  · have he : k = (2117 : Fin 2886) := Fin.ext h2117
    subst k
    rw [keyMomentRowsAt2117]
    exact keyMoment2117 B hB
  · have he : k = (2118 : Fin 2886) := Fin.ext h2118
    subst k
    rw [keyMomentRowsAt2118]
    exact keyMoment2118 B hB
  · have he : k = (2119 : Fin 2886) := Fin.ext h2119
    subst k
    rw [keyMomentRowsAt2119]
    exact keyMoment2119 B hB
  · have he : k = (2120 : Fin 2886) := Fin.ext h2120
    subst k
    rw [keyMomentRowsAt2120]
    exact keyMoment2120 B hB
  · have he : k = (2121 : Fin 2886) := Fin.ext h2121
    subst k
    rw [keyMomentRowsAt2121]
    exact keyMoment2121 B hB
  · have he : k = (2122 : Fin 2886) := Fin.ext h2122
    subst k
    rw [keyMomentRowsAt2122]
    exact keyMoment2122 B hB
  · have he : k = (2123 : Fin 2886) := Fin.ext h2123
    subst k
    rw [keyMomentRowsAt2123]
    exact keyMoment2123 B hB
  · have he : k = (2124 : Fin 2886) := Fin.ext h2124
    subst k
    rw [keyMomentRowsAt2124]
    exact keyMoment2124 B hB
  · have he : k = (2125 : Fin 2886) := Fin.ext h2125
    subst k
    rw [keyMomentRowsAt2125]
    exact keyMoment2125 B hB
  · have he : k = (2126 : Fin 2886) := Fin.ext h2126
    subst k
    rw [keyMomentRowsAt2126]
    exact keyMoment2126 B hB
  · have he : k = (2127 : Fin 2886) := Fin.ext h2127
    subst k
    rw [keyMomentRowsAt2127]
    exact keyMoment2127 B hB
  · have he : k = (2128 : Fin 2886) := Fin.ext h2128
    subst k
    rw [keyMomentRowsAt2128]
    exact keyMoment2128 B hB
  · have he : k = (2129 : Fin 2886) := Fin.ext h2129
    subst k
    rw [keyMomentRowsAt2129]
    exact keyMoment2129 B hB
  · have he : k = (2130 : Fin 2886) := Fin.ext h2130
    subst k
    rw [keyMomentRowsAt2130]
    exact keyMoment2130 B hB
  · have he : k = (2131 : Fin 2886) := Fin.ext h2131
    subst k
    rw [keyMomentRowsAt2131]
    exact keyMoment2131 B hB
  · have he : k = (2132 : Fin 2886) := Fin.ext h2132
    subst k
    rw [keyMomentRowsAt2132]
    exact keyMoment2132 B hB
  · have he : k = (2133 : Fin 2886) := Fin.ext h2133
    subst k
    rw [keyMomentRowsAt2133]
    exact keyMoment2133 B hB
  · have he : k = (2134 : Fin 2886) := Fin.ext h2134
    subst k
    rw [keyMomentRowsAt2134]
    exact keyMoment2134 B hB
  · have he : k = (2135 : Fin 2886) := Fin.ext h2135
    subst k
    rw [keyMomentRowsAt2135]
    exact keyMoment2135 B hB
  · have he : k = (2136 : Fin 2886) := Fin.ext h2136
    subst k
    rw [keyMomentRowsAt2136]
    exact keyMoment2136 B hB
  · have he : k = (2137 : Fin 2886) := Fin.ext h2137
    subst k
    rw [keyMomentRowsAt2137]
    exact keyMoment2137 B hB
  · have he : k = (2138 : Fin 2886) := Fin.ext h2138
    subst k
    rw [keyMomentRowsAt2138]
    exact keyMoment2138 B hB
  · have he : k = (2139 : Fin 2886) := Fin.ext h2139
    subst k
    rw [keyMomentRowsAt2139]
    exact keyMoment2139 B hB
  · have he : k = (2140 : Fin 2886) := Fin.ext h2140
    subst k
    rw [keyMomentRowsAt2140]
    exact keyMoment2140 B hB
  · have he : k = (2141 : Fin 2886) := Fin.ext h2141
    subst k
    rw [keyMomentRowsAt2141]
    exact keyMoment2141 B hB
  · have he : k = (2142 : Fin 2886) := Fin.ext h2142
    subst k
    rw [keyMomentRowsAt2142]
    exact keyMoment2142 B hB
  · have he : k = (2143 : Fin 2886) := Fin.ext h2143
    subst k
    rw [keyMomentRowsAt2143]
    exact keyMoment2143 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
