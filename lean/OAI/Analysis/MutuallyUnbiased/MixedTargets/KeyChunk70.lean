import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound70
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2240 : keyMomentRows (2240 : Fin 2886) =
    keyMomentRow2240 := by decide +kernel

theorem keyMomentRowsAt2241 : keyMomentRows (2241 : Fin 2886) =
    keyMomentRow2241 := by decide +kernel

theorem keyMomentRowsAt2242 : keyMomentRows (2242 : Fin 2886) =
    keyMomentRow2242 := by decide +kernel

theorem keyMomentRowsAt2243 : keyMomentRows (2243 : Fin 2886) =
    keyMomentRow2243 := by decide +kernel

theorem keyMomentRowsAt2244 : keyMomentRows (2244 : Fin 2886) =
    keyMomentRow2244 := by decide +kernel

theorem keyMomentRowsAt2245 : keyMomentRows (2245 : Fin 2886) =
    keyMomentRow2245 := by decide +kernel

theorem keyMomentRowsAt2246 : keyMomentRows (2246 : Fin 2886) =
    keyMomentRow2246 := by decide +kernel

theorem keyMomentRowsAt2247 : keyMomentRows (2247 : Fin 2886) =
    keyMomentRow2247 := by decide +kernel

theorem keyMomentRowsAt2248 : keyMomentRows (2248 : Fin 2886) =
    keyMomentRow2248 := by decide +kernel

theorem keyMomentRowsAt2249 : keyMomentRows (2249 : Fin 2886) =
    keyMomentRow2249 := by decide +kernel

theorem keyMomentRowsAt2250 : keyMomentRows (2250 : Fin 2886) =
    keyMomentRow2250 := by decide +kernel

theorem keyMomentRowsAt2251 : keyMomentRows (2251 : Fin 2886) =
    keyMomentRow2251 := by decide +kernel

theorem keyMomentRowsAt2252 : keyMomentRows (2252 : Fin 2886) =
    keyMomentRow2252 := by decide +kernel

theorem keyMomentRowsAt2253 : keyMomentRows (2253 : Fin 2886) =
    keyMomentRow2253 := by decide +kernel

theorem keyMomentRowsAt2254 : keyMomentRows (2254 : Fin 2886) =
    keyMomentRow2254 := by decide +kernel

theorem keyMomentRowsAt2255 : keyMomentRows (2255 : Fin 2886) =
    keyMomentRow2255 := by decide +kernel

theorem keyMomentRowsAt2256 : keyMomentRows (2256 : Fin 2886) =
    keyMomentRow2256 := by decide +kernel

theorem keyMomentRowsAt2257 : keyMomentRows (2257 : Fin 2886) =
    keyMomentRow2257 := by decide +kernel

theorem keyMomentRowsAt2258 : keyMomentRows (2258 : Fin 2886) =
    keyMomentRow2258 := by decide +kernel

theorem keyMomentRowsAt2259 : keyMomentRows (2259 : Fin 2886) =
    keyMomentRow2259 := by decide +kernel

theorem keyMomentRowsAt2260 : keyMomentRows (2260 : Fin 2886) =
    keyMomentRow2260 := by decide +kernel

theorem keyMomentRowsAt2261 : keyMomentRows (2261 : Fin 2886) =
    keyMomentRow2261 := by decide +kernel

theorem keyMomentRowsAt2262 : keyMomentRows (2262 : Fin 2886) =
    keyMomentRow2262 := by decide +kernel

theorem keyMomentRowsAt2263 : keyMomentRows (2263 : Fin 2886) =
    keyMomentRow2263 := by decide +kernel

theorem keyMomentRowsAt2264 : keyMomentRows (2264 : Fin 2886) =
    keyMomentRow2264 := by decide +kernel

theorem keyMomentRowsAt2265 : keyMomentRows (2265 : Fin 2886) =
    keyMomentRow2265 := by decide +kernel

theorem keyMomentRowsAt2266 : keyMomentRows (2266 : Fin 2886) =
    keyMomentRow2266 := by decide +kernel

theorem keyMomentRowsAt2267 : keyMomentRows (2267 : Fin 2886) =
    keyMomentRow2267 := by decide +kernel

theorem keyMomentRowsAt2268 : keyMomentRows (2268 : Fin 2886) =
    keyMomentRow2268 := by decide +kernel

theorem keyMomentRowsAt2269 : keyMomentRows (2269 : Fin 2886) =
    keyMomentRow2269 := by decide +kernel

theorem keyMomentRowsAt2270 : keyMomentRows (2270 : Fin 2886) =
    keyMomentRow2270 := by decide +kernel

theorem keyMomentRowsAt2271 : keyMomentRows (2271 : Fin 2886) =
    keyMomentRow2271 := by decide +kernel

theorem keyMomentChunkSound70 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 70) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2240 ∨ k.val = 2241 ∨ k.val = 2242 ∨ k.val = 2243 ∨ k.val = 2244 ∨ k.val = 2245 ∨ k.val = 2246 ∨ k.val = 2247 ∨ k.val = 2248 ∨ k.val = 2249 ∨ k.val = 2250 ∨ k.val = 2251 ∨ k.val = 2252 ∨ k.val = 2253 ∨ k.val = 2254 ∨ k.val = 2255 ∨ k.val = 2256 ∨ k.val = 2257 ∨ k.val = 2258 ∨ k.val = 2259 ∨ k.val = 2260 ∨ k.val = 2261 ∨ k.val = 2262 ∨ k.val = 2263 ∨ k.val = 2264 ∨ k.val = 2265 ∨ k.val = 2266 ∨ k.val = 2267 ∨ k.val = 2268 ∨ k.val = 2269 ∨ k.val = 2270 ∨ k.val = 2271 := by omega
  rcases heq with h2240 | h2241 | h2242 | h2243 | h2244 | h2245 | h2246 | h2247 | h2248 | h2249 | h2250 | h2251 | h2252 | h2253 | h2254 | h2255 | h2256 | h2257 | h2258 | h2259 | h2260 | h2261 | h2262 | h2263 | h2264 | h2265 | h2266 | h2267 | h2268 | h2269 | h2270 | h2271
  · have he : k = (2240 : Fin 2886) := Fin.ext h2240
    subst k
    rw [keyMomentRowsAt2240]
    exact keyMoment2240 B hB
  · have he : k = (2241 : Fin 2886) := Fin.ext h2241
    subst k
    rw [keyMomentRowsAt2241]
    exact keyMoment2241 B hB
  · have he : k = (2242 : Fin 2886) := Fin.ext h2242
    subst k
    rw [keyMomentRowsAt2242]
    exact keyMoment2242 B hB
  · have he : k = (2243 : Fin 2886) := Fin.ext h2243
    subst k
    rw [keyMomentRowsAt2243]
    exact keyMoment2243 B hB
  · have he : k = (2244 : Fin 2886) := Fin.ext h2244
    subst k
    rw [keyMomentRowsAt2244]
    exact keyMoment2244 B hB
  · have he : k = (2245 : Fin 2886) := Fin.ext h2245
    subst k
    rw [keyMomentRowsAt2245]
    exact keyMoment2245 B hB
  · have he : k = (2246 : Fin 2886) := Fin.ext h2246
    subst k
    rw [keyMomentRowsAt2246]
    exact keyMoment2246 B hB
  · have he : k = (2247 : Fin 2886) := Fin.ext h2247
    subst k
    rw [keyMomentRowsAt2247]
    exact keyMoment2247 B hB
  · have he : k = (2248 : Fin 2886) := Fin.ext h2248
    subst k
    rw [keyMomentRowsAt2248]
    exact keyMoment2248 B hB
  · have he : k = (2249 : Fin 2886) := Fin.ext h2249
    subst k
    rw [keyMomentRowsAt2249]
    exact keyMoment2249 B hB
  · have he : k = (2250 : Fin 2886) := Fin.ext h2250
    subst k
    rw [keyMomentRowsAt2250]
    exact keyMoment2250 B hB
  · have he : k = (2251 : Fin 2886) := Fin.ext h2251
    subst k
    rw [keyMomentRowsAt2251]
    exact keyMoment2251 B hB
  · have he : k = (2252 : Fin 2886) := Fin.ext h2252
    subst k
    rw [keyMomentRowsAt2252]
    exact keyMoment2252 B hB
  · have he : k = (2253 : Fin 2886) := Fin.ext h2253
    subst k
    rw [keyMomentRowsAt2253]
    exact keyMoment2253 B hB
  · have he : k = (2254 : Fin 2886) := Fin.ext h2254
    subst k
    rw [keyMomentRowsAt2254]
    exact keyMoment2254 B hB
  · have he : k = (2255 : Fin 2886) := Fin.ext h2255
    subst k
    rw [keyMomentRowsAt2255]
    exact keyMoment2255 B hB
  · have he : k = (2256 : Fin 2886) := Fin.ext h2256
    subst k
    rw [keyMomentRowsAt2256]
    exact keyMoment2256 B hB
  · have he : k = (2257 : Fin 2886) := Fin.ext h2257
    subst k
    rw [keyMomentRowsAt2257]
    exact keyMoment2257 B hB
  · have he : k = (2258 : Fin 2886) := Fin.ext h2258
    subst k
    rw [keyMomentRowsAt2258]
    exact keyMoment2258 B hB
  · have he : k = (2259 : Fin 2886) := Fin.ext h2259
    subst k
    rw [keyMomentRowsAt2259]
    exact keyMoment2259 B hB
  · have he : k = (2260 : Fin 2886) := Fin.ext h2260
    subst k
    rw [keyMomentRowsAt2260]
    exact keyMoment2260 B hB
  · have he : k = (2261 : Fin 2886) := Fin.ext h2261
    subst k
    rw [keyMomentRowsAt2261]
    exact keyMoment2261 B hB
  · have he : k = (2262 : Fin 2886) := Fin.ext h2262
    subst k
    rw [keyMomentRowsAt2262]
    exact keyMoment2262 B hB
  · have he : k = (2263 : Fin 2886) := Fin.ext h2263
    subst k
    rw [keyMomentRowsAt2263]
    exact keyMoment2263 B hB
  · have he : k = (2264 : Fin 2886) := Fin.ext h2264
    subst k
    rw [keyMomentRowsAt2264]
    exact keyMoment2264 B hB
  · have he : k = (2265 : Fin 2886) := Fin.ext h2265
    subst k
    rw [keyMomentRowsAt2265]
    exact keyMoment2265 B hB
  · have he : k = (2266 : Fin 2886) := Fin.ext h2266
    subst k
    rw [keyMomentRowsAt2266]
    exact keyMoment2266 B hB
  · have he : k = (2267 : Fin 2886) := Fin.ext h2267
    subst k
    rw [keyMomentRowsAt2267]
    exact keyMoment2267 B hB
  · have he : k = (2268 : Fin 2886) := Fin.ext h2268
    subst k
    rw [keyMomentRowsAt2268]
    exact keyMoment2268 B hB
  · have he : k = (2269 : Fin 2886) := Fin.ext h2269
    subst k
    rw [keyMomentRowsAt2269]
    exact keyMoment2269 B hB
  · have he : k = (2270 : Fin 2886) := Fin.ext h2270
    subst k
    rw [keyMomentRowsAt2270]
    exact keyMoment2270 B hB
  · have he : k = (2271 : Fin 2886) := Fin.ext h2271
    subst k
    rw [keyMomentRowsAt2271]
    exact keyMoment2271 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
