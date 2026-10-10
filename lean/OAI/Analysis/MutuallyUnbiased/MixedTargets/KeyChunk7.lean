import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound7
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt224 : keyMomentRows (224 : Fin 2886) =
    keyMomentRow224 := by decide +kernel

theorem keyMomentRowsAt225 : keyMomentRows (225 : Fin 2886) =
    keyMomentRow225 := by decide +kernel

theorem keyMomentRowsAt226 : keyMomentRows (226 : Fin 2886) =
    keyMomentRow226 := by decide +kernel

theorem keyMomentRowsAt227 : keyMomentRows (227 : Fin 2886) =
    keyMomentRow227 := by decide +kernel

theorem keyMomentRowsAt228 : keyMomentRows (228 : Fin 2886) =
    keyMomentRow228 := by decide +kernel

theorem keyMomentRowsAt229 : keyMomentRows (229 : Fin 2886) =
    keyMomentRow229 := by decide +kernel

theorem keyMomentRowsAt230 : keyMomentRows (230 : Fin 2886) =
    keyMomentRow230 := by decide +kernel

theorem keyMomentRowsAt231 : keyMomentRows (231 : Fin 2886) =
    keyMomentRow231 := by decide +kernel

theorem keyMomentRowsAt232 : keyMomentRows (232 : Fin 2886) =
    keyMomentRow232 := by decide +kernel

theorem keyMomentRowsAt233 : keyMomentRows (233 : Fin 2886) =
    keyMomentRow233 := by decide +kernel

theorem keyMomentRowsAt234 : keyMomentRows (234 : Fin 2886) =
    keyMomentRow234 := by decide +kernel

theorem keyMomentRowsAt235 : keyMomentRows (235 : Fin 2886) =
    keyMomentRow235 := by decide +kernel

theorem keyMomentRowsAt236 : keyMomentRows (236 : Fin 2886) =
    keyMomentRow236 := by decide +kernel

theorem keyMomentRowsAt237 : keyMomentRows (237 : Fin 2886) =
    keyMomentRow237 := by decide +kernel

theorem keyMomentRowsAt238 : keyMomentRows (238 : Fin 2886) =
    keyMomentRow238 := by decide +kernel

theorem keyMomentRowsAt239 : keyMomentRows (239 : Fin 2886) =
    keyMomentRow239 := by decide +kernel

theorem keyMomentRowsAt240 : keyMomentRows (240 : Fin 2886) =
    keyMomentRow240 := by decide +kernel

theorem keyMomentRowsAt241 : keyMomentRows (241 : Fin 2886) =
    keyMomentRow241 := by decide +kernel

theorem keyMomentRowsAt242 : keyMomentRows (242 : Fin 2886) =
    keyMomentRow242 := by decide +kernel

theorem keyMomentRowsAt243 : keyMomentRows (243 : Fin 2886) =
    keyMomentRow243 := by decide +kernel

theorem keyMomentRowsAt244 : keyMomentRows (244 : Fin 2886) =
    keyMomentRow244 := by decide +kernel

theorem keyMomentRowsAt245 : keyMomentRows (245 : Fin 2886) =
    keyMomentRow245 := by decide +kernel

theorem keyMomentRowsAt246 : keyMomentRows (246 : Fin 2886) =
    keyMomentRow246 := by decide +kernel

theorem keyMomentRowsAt247 : keyMomentRows (247 : Fin 2886) =
    keyMomentRow247 := by decide +kernel

theorem keyMomentRowsAt248 : keyMomentRows (248 : Fin 2886) =
    keyMomentRow248 := by decide +kernel

theorem keyMomentRowsAt249 : keyMomentRows (249 : Fin 2886) =
    keyMomentRow249 := by decide +kernel

theorem keyMomentRowsAt250 : keyMomentRows (250 : Fin 2886) =
    keyMomentRow250 := by decide +kernel

theorem keyMomentRowsAt251 : keyMomentRows (251 : Fin 2886) =
    keyMomentRow251 := by decide +kernel

theorem keyMomentRowsAt252 : keyMomentRows (252 : Fin 2886) =
    keyMomentRow252 := by decide +kernel

theorem keyMomentRowsAt253 : keyMomentRows (253 : Fin 2886) =
    keyMomentRow253 := by decide +kernel

theorem keyMomentRowsAt254 : keyMomentRows (254 : Fin 2886) =
    keyMomentRow254 := by decide +kernel

theorem keyMomentRowsAt255 : keyMomentRows (255 : Fin 2886) =
    keyMomentRow255 := by decide +kernel

theorem keyMomentChunkSound7 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 7) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 224 ∨ k.val = 225 ∨ k.val = 226 ∨ k.val = 227 ∨ k.val = 228 ∨ k.val = 229 ∨ k.val = 230 ∨ k.val = 231 ∨ k.val = 232 ∨ k.val = 233 ∨ k.val = 234 ∨ k.val = 235 ∨ k.val = 236 ∨ k.val = 237 ∨ k.val = 238 ∨ k.val = 239 ∨ k.val = 240 ∨ k.val = 241 ∨ k.val = 242 ∨ k.val = 243 ∨ k.val = 244 ∨ k.val = 245 ∨ k.val = 246 ∨ k.val = 247 ∨ k.val = 248 ∨ k.val = 249 ∨ k.val = 250 ∨ k.val = 251 ∨ k.val = 252 ∨ k.val = 253 ∨ k.val = 254 ∨ k.val = 255 := by omega
  rcases heq with h224 | h225 | h226 | h227 | h228 | h229 | h230 | h231 | h232 | h233 | h234 | h235 | h236 | h237 | h238 | h239 | h240 | h241 | h242 | h243 | h244 | h245 | h246 | h247 | h248 | h249 | h250 | h251 | h252 | h253 | h254 | h255
  · have he : k = (224 : Fin 2886) := Fin.ext h224
    subst k
    rw [keyMomentRowsAt224]
    exact keyMoment224 B hB
  · have he : k = (225 : Fin 2886) := Fin.ext h225
    subst k
    rw [keyMomentRowsAt225]
    exact keyMoment225 B hB
  · have he : k = (226 : Fin 2886) := Fin.ext h226
    subst k
    rw [keyMomentRowsAt226]
    exact keyMoment226 B hB
  · have he : k = (227 : Fin 2886) := Fin.ext h227
    subst k
    rw [keyMomentRowsAt227]
    exact keyMoment227 B hB
  · have he : k = (228 : Fin 2886) := Fin.ext h228
    subst k
    rw [keyMomentRowsAt228]
    exact keyMoment228 B hB
  · have he : k = (229 : Fin 2886) := Fin.ext h229
    subst k
    rw [keyMomentRowsAt229]
    exact keyMoment229 B hB
  · have he : k = (230 : Fin 2886) := Fin.ext h230
    subst k
    rw [keyMomentRowsAt230]
    exact keyMoment230 B hB
  · have he : k = (231 : Fin 2886) := Fin.ext h231
    subst k
    rw [keyMomentRowsAt231]
    exact keyMoment231 B hB
  · have he : k = (232 : Fin 2886) := Fin.ext h232
    subst k
    rw [keyMomentRowsAt232]
    exact keyMoment232 B hB
  · have he : k = (233 : Fin 2886) := Fin.ext h233
    subst k
    rw [keyMomentRowsAt233]
    exact keyMoment233 B hB
  · have he : k = (234 : Fin 2886) := Fin.ext h234
    subst k
    rw [keyMomentRowsAt234]
    exact keyMoment234 B hB
  · have he : k = (235 : Fin 2886) := Fin.ext h235
    subst k
    rw [keyMomentRowsAt235]
    exact keyMoment235 B hB
  · have he : k = (236 : Fin 2886) := Fin.ext h236
    subst k
    rw [keyMomentRowsAt236]
    exact keyMoment236 B hB
  · have he : k = (237 : Fin 2886) := Fin.ext h237
    subst k
    rw [keyMomentRowsAt237]
    exact keyMoment237 B hB
  · have he : k = (238 : Fin 2886) := Fin.ext h238
    subst k
    rw [keyMomentRowsAt238]
    exact keyMoment238 B hB
  · have he : k = (239 : Fin 2886) := Fin.ext h239
    subst k
    rw [keyMomentRowsAt239]
    exact keyMoment239 B hB
  · have he : k = (240 : Fin 2886) := Fin.ext h240
    subst k
    rw [keyMomentRowsAt240]
    exact keyMoment240 B hB
  · have he : k = (241 : Fin 2886) := Fin.ext h241
    subst k
    rw [keyMomentRowsAt241]
    exact keyMoment241 B hB
  · have he : k = (242 : Fin 2886) := Fin.ext h242
    subst k
    rw [keyMomentRowsAt242]
    exact keyMoment242 B hB
  · have he : k = (243 : Fin 2886) := Fin.ext h243
    subst k
    rw [keyMomentRowsAt243]
    exact keyMoment243 B hB
  · have he : k = (244 : Fin 2886) := Fin.ext h244
    subst k
    rw [keyMomentRowsAt244]
    exact keyMoment244 B hB
  · have he : k = (245 : Fin 2886) := Fin.ext h245
    subst k
    rw [keyMomentRowsAt245]
    exact keyMoment245 B hB
  · have he : k = (246 : Fin 2886) := Fin.ext h246
    subst k
    rw [keyMomentRowsAt246]
    exact keyMoment246 B hB
  · have he : k = (247 : Fin 2886) := Fin.ext h247
    subst k
    rw [keyMomentRowsAt247]
    exact keyMoment247 B hB
  · have he : k = (248 : Fin 2886) := Fin.ext h248
    subst k
    rw [keyMomentRowsAt248]
    exact keyMoment248 B hB
  · have he : k = (249 : Fin 2886) := Fin.ext h249
    subst k
    rw [keyMomentRowsAt249]
    exact keyMoment249 B hB
  · have he : k = (250 : Fin 2886) := Fin.ext h250
    subst k
    rw [keyMomentRowsAt250]
    exact keyMoment250 B hB
  · have he : k = (251 : Fin 2886) := Fin.ext h251
    subst k
    rw [keyMomentRowsAt251]
    exact keyMoment251 B hB
  · have he : k = (252 : Fin 2886) := Fin.ext h252
    subst k
    rw [keyMomentRowsAt252]
    exact keyMoment252 B hB
  · have he : k = (253 : Fin 2886) := Fin.ext h253
    subst k
    rw [keyMomentRowsAt253]
    exact keyMoment253 B hB
  · have he : k = (254 : Fin 2886) := Fin.ext h254
    subst k
    rw [keyMomentRowsAt254]
    exact keyMoment254 B hB
  · have he : k = (255 : Fin 2886) := Fin.ext h255
    subst k
    rw [keyMomentRowsAt255]
    exact keyMoment255 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
