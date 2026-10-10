import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound68
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2176 : keyMomentRows (2176 : Fin 2886) =
    keyMomentRow2176 := by decide +kernel

theorem keyMomentRowsAt2177 : keyMomentRows (2177 : Fin 2886) =
    keyMomentRow2177 := by decide +kernel

theorem keyMomentRowsAt2178 : keyMomentRows (2178 : Fin 2886) =
    keyMomentRow2178 := by decide +kernel

theorem keyMomentRowsAt2179 : keyMomentRows (2179 : Fin 2886) =
    keyMomentRow2179 := by decide +kernel

theorem keyMomentRowsAt2180 : keyMomentRows (2180 : Fin 2886) =
    keyMomentRow2180 := by decide +kernel

theorem keyMomentRowsAt2181 : keyMomentRows (2181 : Fin 2886) =
    keyMomentRow2181 := by decide +kernel

theorem keyMomentRowsAt2182 : keyMomentRows (2182 : Fin 2886) =
    keyMomentRow2182 := by decide +kernel

theorem keyMomentRowsAt2183 : keyMomentRows (2183 : Fin 2886) =
    keyMomentRow2183 := by decide +kernel

theorem keyMomentRowsAt2184 : keyMomentRows (2184 : Fin 2886) =
    keyMomentRow2184 := by decide +kernel

theorem keyMomentRowsAt2185 : keyMomentRows (2185 : Fin 2886) =
    keyMomentRow2185 := by decide +kernel

theorem keyMomentRowsAt2186 : keyMomentRows (2186 : Fin 2886) =
    keyMomentRow2186 := by decide +kernel

theorem keyMomentRowsAt2187 : keyMomentRows (2187 : Fin 2886) =
    keyMomentRow2187 := by decide +kernel

theorem keyMomentRowsAt2188 : keyMomentRows (2188 : Fin 2886) =
    keyMomentRow2188 := by decide +kernel

theorem keyMomentRowsAt2189 : keyMomentRows (2189 : Fin 2886) =
    keyMomentRow2189 := by decide +kernel

theorem keyMomentRowsAt2190 : keyMomentRows (2190 : Fin 2886) =
    keyMomentRow2190 := by decide +kernel

theorem keyMomentRowsAt2191 : keyMomentRows (2191 : Fin 2886) =
    keyMomentRow2191 := by decide +kernel

theorem keyMomentRowsAt2192 : keyMomentRows (2192 : Fin 2886) =
    keyMomentRow2192 := by decide +kernel

theorem keyMomentRowsAt2193 : keyMomentRows (2193 : Fin 2886) =
    keyMomentRow2193 := by decide +kernel

theorem keyMomentRowsAt2194 : keyMomentRows (2194 : Fin 2886) =
    keyMomentRow2194 := by decide +kernel

theorem keyMomentRowsAt2195 : keyMomentRows (2195 : Fin 2886) =
    keyMomentRow2195 := by decide +kernel

theorem keyMomentRowsAt2196 : keyMomentRows (2196 : Fin 2886) =
    keyMomentRow2196 := by decide +kernel

theorem keyMomentRowsAt2197 : keyMomentRows (2197 : Fin 2886) =
    keyMomentRow2197 := by decide +kernel

theorem keyMomentRowsAt2198 : keyMomentRows (2198 : Fin 2886) =
    keyMomentRow2198 := by decide +kernel

theorem keyMomentRowsAt2199 : keyMomentRows (2199 : Fin 2886) =
    keyMomentRow2199 := by decide +kernel

theorem keyMomentRowsAt2200 : keyMomentRows (2200 : Fin 2886) =
    keyMomentRow2200 := by decide +kernel

theorem keyMomentRowsAt2201 : keyMomentRows (2201 : Fin 2886) =
    keyMomentRow2201 := by decide +kernel

theorem keyMomentRowsAt2202 : keyMomentRows (2202 : Fin 2886) =
    keyMomentRow2202 := by decide +kernel

theorem keyMomentRowsAt2203 : keyMomentRows (2203 : Fin 2886) =
    keyMomentRow2203 := by decide +kernel

theorem keyMomentRowsAt2204 : keyMomentRows (2204 : Fin 2886) =
    keyMomentRow2204 := by decide +kernel

theorem keyMomentRowsAt2205 : keyMomentRows (2205 : Fin 2886) =
    keyMomentRow2205 := by decide +kernel

theorem keyMomentRowsAt2206 : keyMomentRows (2206 : Fin 2886) =
    keyMomentRow2206 := by decide +kernel

theorem keyMomentRowsAt2207 : keyMomentRows (2207 : Fin 2886) =
    keyMomentRow2207 := by decide +kernel

theorem keyMomentChunkSound68 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 68) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2176 ∨ k.val = 2177 ∨ k.val = 2178 ∨ k.val = 2179 ∨ k.val = 2180 ∨ k.val = 2181 ∨ k.val = 2182 ∨ k.val = 2183 ∨ k.val = 2184 ∨ k.val = 2185 ∨ k.val = 2186 ∨ k.val = 2187 ∨ k.val = 2188 ∨ k.val = 2189 ∨ k.val = 2190 ∨ k.val = 2191 ∨ k.val = 2192 ∨ k.val = 2193 ∨ k.val = 2194 ∨ k.val = 2195 ∨ k.val = 2196 ∨ k.val = 2197 ∨ k.val = 2198 ∨ k.val = 2199 ∨ k.val = 2200 ∨ k.val = 2201 ∨ k.val = 2202 ∨ k.val = 2203 ∨ k.val = 2204 ∨ k.val = 2205 ∨ k.val = 2206 ∨ k.val = 2207 := by omega
  rcases heq with h2176 | h2177 | h2178 | h2179 | h2180 | h2181 | h2182 | h2183 | h2184 | h2185 | h2186 | h2187 | h2188 | h2189 | h2190 | h2191 | h2192 | h2193 | h2194 | h2195 | h2196 | h2197 | h2198 | h2199 | h2200 | h2201 | h2202 | h2203 | h2204 | h2205 | h2206 | h2207
  · have he : k = (2176 : Fin 2886) := Fin.ext h2176
    subst k
    rw [keyMomentRowsAt2176]
    exact keyMoment2176 B hB
  · have he : k = (2177 : Fin 2886) := Fin.ext h2177
    subst k
    rw [keyMomentRowsAt2177]
    exact keyMoment2177 B hB
  · have he : k = (2178 : Fin 2886) := Fin.ext h2178
    subst k
    rw [keyMomentRowsAt2178]
    exact keyMoment2178 B hB
  · have he : k = (2179 : Fin 2886) := Fin.ext h2179
    subst k
    rw [keyMomentRowsAt2179]
    exact keyMoment2179 B hB
  · have he : k = (2180 : Fin 2886) := Fin.ext h2180
    subst k
    rw [keyMomentRowsAt2180]
    exact keyMoment2180 B hB
  · have he : k = (2181 : Fin 2886) := Fin.ext h2181
    subst k
    rw [keyMomentRowsAt2181]
    exact keyMoment2181 B hB
  · have he : k = (2182 : Fin 2886) := Fin.ext h2182
    subst k
    rw [keyMomentRowsAt2182]
    exact keyMoment2182 B hB
  · have he : k = (2183 : Fin 2886) := Fin.ext h2183
    subst k
    rw [keyMomentRowsAt2183]
    exact keyMoment2183 B hB
  · have he : k = (2184 : Fin 2886) := Fin.ext h2184
    subst k
    rw [keyMomentRowsAt2184]
    exact keyMoment2184 B hB
  · have he : k = (2185 : Fin 2886) := Fin.ext h2185
    subst k
    rw [keyMomentRowsAt2185]
    exact keyMoment2185 B hB
  · have he : k = (2186 : Fin 2886) := Fin.ext h2186
    subst k
    rw [keyMomentRowsAt2186]
    exact keyMoment2186 B hB
  · have he : k = (2187 : Fin 2886) := Fin.ext h2187
    subst k
    rw [keyMomentRowsAt2187]
    exact keyMoment2187 B hB
  · have he : k = (2188 : Fin 2886) := Fin.ext h2188
    subst k
    rw [keyMomentRowsAt2188]
    exact keyMoment2188 B hB
  · have he : k = (2189 : Fin 2886) := Fin.ext h2189
    subst k
    rw [keyMomentRowsAt2189]
    exact keyMoment2189 B hB
  · have he : k = (2190 : Fin 2886) := Fin.ext h2190
    subst k
    rw [keyMomentRowsAt2190]
    exact keyMoment2190 B hB
  · have he : k = (2191 : Fin 2886) := Fin.ext h2191
    subst k
    rw [keyMomentRowsAt2191]
    exact keyMoment2191 B hB
  · have he : k = (2192 : Fin 2886) := Fin.ext h2192
    subst k
    rw [keyMomentRowsAt2192]
    exact keyMoment2192 B hB
  · have he : k = (2193 : Fin 2886) := Fin.ext h2193
    subst k
    rw [keyMomentRowsAt2193]
    exact keyMoment2193 B hB
  · have he : k = (2194 : Fin 2886) := Fin.ext h2194
    subst k
    rw [keyMomentRowsAt2194]
    exact keyMoment2194 B hB
  · have he : k = (2195 : Fin 2886) := Fin.ext h2195
    subst k
    rw [keyMomentRowsAt2195]
    exact keyMoment2195 B hB
  · have he : k = (2196 : Fin 2886) := Fin.ext h2196
    subst k
    rw [keyMomentRowsAt2196]
    exact keyMoment2196 B hB
  · have he : k = (2197 : Fin 2886) := Fin.ext h2197
    subst k
    rw [keyMomentRowsAt2197]
    exact keyMoment2197 B hB
  · have he : k = (2198 : Fin 2886) := Fin.ext h2198
    subst k
    rw [keyMomentRowsAt2198]
    exact keyMoment2198 B hB
  · have he : k = (2199 : Fin 2886) := Fin.ext h2199
    subst k
    rw [keyMomentRowsAt2199]
    exact keyMoment2199 B hB
  · have he : k = (2200 : Fin 2886) := Fin.ext h2200
    subst k
    rw [keyMomentRowsAt2200]
    exact keyMoment2200 B hB
  · have he : k = (2201 : Fin 2886) := Fin.ext h2201
    subst k
    rw [keyMomentRowsAt2201]
    exact keyMoment2201 B hB
  · have he : k = (2202 : Fin 2886) := Fin.ext h2202
    subst k
    rw [keyMomentRowsAt2202]
    exact keyMoment2202 B hB
  · have he : k = (2203 : Fin 2886) := Fin.ext h2203
    subst k
    rw [keyMomentRowsAt2203]
    exact keyMoment2203 B hB
  · have he : k = (2204 : Fin 2886) := Fin.ext h2204
    subst k
    rw [keyMomentRowsAt2204]
    exact keyMoment2204 B hB
  · have he : k = (2205 : Fin 2886) := Fin.ext h2205
    subst k
    rw [keyMomentRowsAt2205]
    exact keyMoment2205 B hB
  · have he : k = (2206 : Fin 2886) := Fin.ext h2206
    subst k
    rw [keyMomentRowsAt2206]
    exact keyMoment2206 B hB
  · have he : k = (2207 : Fin 2886) := Fin.ext h2207
    subst k
    rw [keyMomentRowsAt2207]
    exact keyMoment2207 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
