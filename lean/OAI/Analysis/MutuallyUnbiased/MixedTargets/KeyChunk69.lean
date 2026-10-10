import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound69
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2208 : keyMomentRows (2208 : Fin 2886) =
    keyMomentRow2208 := by decide +kernel

theorem keyMomentRowsAt2209 : keyMomentRows (2209 : Fin 2886) =
    keyMomentRow2209 := by decide +kernel

theorem keyMomentRowsAt2210 : keyMomentRows (2210 : Fin 2886) =
    keyMomentRow2210 := by decide +kernel

theorem keyMomentRowsAt2211 : keyMomentRows (2211 : Fin 2886) =
    keyMomentRow2211 := by decide +kernel

theorem keyMomentRowsAt2212 : keyMomentRows (2212 : Fin 2886) =
    keyMomentRow2212 := by decide +kernel

theorem keyMomentRowsAt2213 : keyMomentRows (2213 : Fin 2886) =
    keyMomentRow2213 := by decide +kernel

theorem keyMomentRowsAt2214 : keyMomentRows (2214 : Fin 2886) =
    keyMomentRow2214 := by decide +kernel

theorem keyMomentRowsAt2215 : keyMomentRows (2215 : Fin 2886) =
    keyMomentRow2215 := by decide +kernel

theorem keyMomentRowsAt2216 : keyMomentRows (2216 : Fin 2886) =
    keyMomentRow2216 := by decide +kernel

theorem keyMomentRowsAt2217 : keyMomentRows (2217 : Fin 2886) =
    keyMomentRow2217 := by decide +kernel

theorem keyMomentRowsAt2218 : keyMomentRows (2218 : Fin 2886) =
    keyMomentRow2218 := by decide +kernel

theorem keyMomentRowsAt2219 : keyMomentRows (2219 : Fin 2886) =
    keyMomentRow2219 := by decide +kernel

theorem keyMomentRowsAt2220 : keyMomentRows (2220 : Fin 2886) =
    keyMomentRow2220 := by decide +kernel

theorem keyMomentRowsAt2221 : keyMomentRows (2221 : Fin 2886) =
    keyMomentRow2221 := by decide +kernel

theorem keyMomentRowsAt2222 : keyMomentRows (2222 : Fin 2886) =
    keyMomentRow2222 := by decide +kernel

theorem keyMomentRowsAt2223 : keyMomentRows (2223 : Fin 2886) =
    keyMomentRow2223 := by decide +kernel

theorem keyMomentRowsAt2224 : keyMomentRows (2224 : Fin 2886) =
    keyMomentRow2224 := by decide +kernel

theorem keyMomentRowsAt2225 : keyMomentRows (2225 : Fin 2886) =
    keyMomentRow2225 := by decide +kernel

theorem keyMomentRowsAt2226 : keyMomentRows (2226 : Fin 2886) =
    keyMomentRow2226 := by decide +kernel

theorem keyMomentRowsAt2227 : keyMomentRows (2227 : Fin 2886) =
    keyMomentRow2227 := by decide +kernel

theorem keyMomentRowsAt2228 : keyMomentRows (2228 : Fin 2886) =
    keyMomentRow2228 := by decide +kernel

theorem keyMomentRowsAt2229 : keyMomentRows (2229 : Fin 2886) =
    keyMomentRow2229 := by decide +kernel

theorem keyMomentRowsAt2230 : keyMomentRows (2230 : Fin 2886) =
    keyMomentRow2230 := by decide +kernel

theorem keyMomentRowsAt2231 : keyMomentRows (2231 : Fin 2886) =
    keyMomentRow2231 := by decide +kernel

theorem keyMomentRowsAt2232 : keyMomentRows (2232 : Fin 2886) =
    keyMomentRow2232 := by decide +kernel

theorem keyMomentRowsAt2233 : keyMomentRows (2233 : Fin 2886) =
    keyMomentRow2233 := by decide +kernel

theorem keyMomentRowsAt2234 : keyMomentRows (2234 : Fin 2886) =
    keyMomentRow2234 := by decide +kernel

theorem keyMomentRowsAt2235 : keyMomentRows (2235 : Fin 2886) =
    keyMomentRow2235 := by decide +kernel

theorem keyMomentRowsAt2236 : keyMomentRows (2236 : Fin 2886) =
    keyMomentRow2236 := by decide +kernel

theorem keyMomentRowsAt2237 : keyMomentRows (2237 : Fin 2886) =
    keyMomentRow2237 := by decide +kernel

theorem keyMomentRowsAt2238 : keyMomentRows (2238 : Fin 2886) =
    keyMomentRow2238 := by decide +kernel

theorem keyMomentRowsAt2239 : keyMomentRows (2239 : Fin 2886) =
    keyMomentRow2239 := by decide +kernel

theorem keyMomentChunkSound69 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 69) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2208 ∨ k.val = 2209 ∨ k.val = 2210 ∨ k.val = 2211 ∨ k.val = 2212 ∨ k.val = 2213 ∨ k.val = 2214 ∨ k.val = 2215 ∨ k.val = 2216 ∨ k.val = 2217 ∨ k.val = 2218 ∨ k.val = 2219 ∨ k.val = 2220 ∨ k.val = 2221 ∨ k.val = 2222 ∨ k.val = 2223 ∨ k.val = 2224 ∨ k.val = 2225 ∨ k.val = 2226 ∨ k.val = 2227 ∨ k.val = 2228 ∨ k.val = 2229 ∨ k.val = 2230 ∨ k.val = 2231 ∨ k.val = 2232 ∨ k.val = 2233 ∨ k.val = 2234 ∨ k.val = 2235 ∨ k.val = 2236 ∨ k.val = 2237 ∨ k.val = 2238 ∨ k.val = 2239 := by omega
  rcases heq with h2208 | h2209 | h2210 | h2211 | h2212 | h2213 | h2214 | h2215 | h2216 | h2217 | h2218 | h2219 | h2220 | h2221 | h2222 | h2223 | h2224 | h2225 | h2226 | h2227 | h2228 | h2229 | h2230 | h2231 | h2232 | h2233 | h2234 | h2235 | h2236 | h2237 | h2238 | h2239
  · have he : k = (2208 : Fin 2886) := Fin.ext h2208
    subst k
    rw [keyMomentRowsAt2208]
    exact keyMoment2208 B hB
  · have he : k = (2209 : Fin 2886) := Fin.ext h2209
    subst k
    rw [keyMomentRowsAt2209]
    exact keyMoment2209 B hB
  · have he : k = (2210 : Fin 2886) := Fin.ext h2210
    subst k
    rw [keyMomentRowsAt2210]
    exact keyMoment2210 B hB
  · have he : k = (2211 : Fin 2886) := Fin.ext h2211
    subst k
    rw [keyMomentRowsAt2211]
    exact keyMoment2211 B hB
  · have he : k = (2212 : Fin 2886) := Fin.ext h2212
    subst k
    rw [keyMomentRowsAt2212]
    exact keyMoment2212 B hB
  · have he : k = (2213 : Fin 2886) := Fin.ext h2213
    subst k
    rw [keyMomentRowsAt2213]
    exact keyMoment2213 B hB
  · have he : k = (2214 : Fin 2886) := Fin.ext h2214
    subst k
    rw [keyMomentRowsAt2214]
    exact keyMoment2214 B hB
  · have he : k = (2215 : Fin 2886) := Fin.ext h2215
    subst k
    rw [keyMomentRowsAt2215]
    exact keyMoment2215 B hB
  · have he : k = (2216 : Fin 2886) := Fin.ext h2216
    subst k
    rw [keyMomentRowsAt2216]
    exact keyMoment2216 B hB
  · have he : k = (2217 : Fin 2886) := Fin.ext h2217
    subst k
    rw [keyMomentRowsAt2217]
    exact keyMoment2217 B hB
  · have he : k = (2218 : Fin 2886) := Fin.ext h2218
    subst k
    rw [keyMomentRowsAt2218]
    exact keyMoment2218 B hB
  · have he : k = (2219 : Fin 2886) := Fin.ext h2219
    subst k
    rw [keyMomentRowsAt2219]
    exact keyMoment2219 B hB
  · have he : k = (2220 : Fin 2886) := Fin.ext h2220
    subst k
    rw [keyMomentRowsAt2220]
    exact keyMoment2220 B hB
  · have he : k = (2221 : Fin 2886) := Fin.ext h2221
    subst k
    rw [keyMomentRowsAt2221]
    exact keyMoment2221 B hB
  · have he : k = (2222 : Fin 2886) := Fin.ext h2222
    subst k
    rw [keyMomentRowsAt2222]
    exact keyMoment2222 B hB
  · have he : k = (2223 : Fin 2886) := Fin.ext h2223
    subst k
    rw [keyMomentRowsAt2223]
    exact keyMoment2223 B hB
  · have he : k = (2224 : Fin 2886) := Fin.ext h2224
    subst k
    rw [keyMomentRowsAt2224]
    exact keyMoment2224 B hB
  · have he : k = (2225 : Fin 2886) := Fin.ext h2225
    subst k
    rw [keyMomentRowsAt2225]
    exact keyMoment2225 B hB
  · have he : k = (2226 : Fin 2886) := Fin.ext h2226
    subst k
    rw [keyMomentRowsAt2226]
    exact keyMoment2226 B hB
  · have he : k = (2227 : Fin 2886) := Fin.ext h2227
    subst k
    rw [keyMomentRowsAt2227]
    exact keyMoment2227 B hB
  · have he : k = (2228 : Fin 2886) := Fin.ext h2228
    subst k
    rw [keyMomentRowsAt2228]
    exact keyMoment2228 B hB
  · have he : k = (2229 : Fin 2886) := Fin.ext h2229
    subst k
    rw [keyMomentRowsAt2229]
    exact keyMoment2229 B hB
  · have he : k = (2230 : Fin 2886) := Fin.ext h2230
    subst k
    rw [keyMomentRowsAt2230]
    exact keyMoment2230 B hB
  · have he : k = (2231 : Fin 2886) := Fin.ext h2231
    subst k
    rw [keyMomentRowsAt2231]
    exact keyMoment2231 B hB
  · have he : k = (2232 : Fin 2886) := Fin.ext h2232
    subst k
    rw [keyMomentRowsAt2232]
    exact keyMoment2232 B hB
  · have he : k = (2233 : Fin 2886) := Fin.ext h2233
    subst k
    rw [keyMomentRowsAt2233]
    exact keyMoment2233 B hB
  · have he : k = (2234 : Fin 2886) := Fin.ext h2234
    subst k
    rw [keyMomentRowsAt2234]
    exact keyMoment2234 B hB
  · have he : k = (2235 : Fin 2886) := Fin.ext h2235
    subst k
    rw [keyMomentRowsAt2235]
    exact keyMoment2235 B hB
  · have he : k = (2236 : Fin 2886) := Fin.ext h2236
    subst k
    rw [keyMomentRowsAt2236]
    exact keyMoment2236 B hB
  · have he : k = (2237 : Fin 2886) := Fin.ext h2237
    subst k
    rw [keyMomentRowsAt2237]
    exact keyMoment2237 B hB
  · have he : k = (2238 : Fin 2886) := Fin.ext h2238
    subst k
    rw [keyMomentRowsAt2238]
    exact keyMoment2238 B hB
  · have he : k = (2239 : Fin 2886) := Fin.ext h2239
    subst k
    rw [keyMomentRowsAt2239]
    exact keyMoment2239 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
