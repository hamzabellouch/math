import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound6
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt192 : keyMomentRows (192 : Fin 2886) =
    keyMomentRow192 := by decide +kernel

theorem keyMomentRowsAt193 : keyMomentRows (193 : Fin 2886) =
    keyMomentRow193 := by decide +kernel

theorem keyMomentRowsAt194 : keyMomentRows (194 : Fin 2886) =
    keyMomentRow194 := by decide +kernel

theorem keyMomentRowsAt195 : keyMomentRows (195 : Fin 2886) =
    keyMomentRow195 := by decide +kernel

theorem keyMomentRowsAt196 : keyMomentRows (196 : Fin 2886) =
    keyMomentRow196 := by decide +kernel

theorem keyMomentRowsAt197 : keyMomentRows (197 : Fin 2886) =
    keyMomentRow197 := by decide +kernel

theorem keyMomentRowsAt198 : keyMomentRows (198 : Fin 2886) =
    keyMomentRow198 := by decide +kernel

theorem keyMomentRowsAt199 : keyMomentRows (199 : Fin 2886) =
    keyMomentRow199 := by decide +kernel

theorem keyMomentRowsAt200 : keyMomentRows (200 : Fin 2886) =
    keyMomentRow200 := by decide +kernel

theorem keyMomentRowsAt201 : keyMomentRows (201 : Fin 2886) =
    keyMomentRow201 := by decide +kernel

theorem keyMomentRowsAt202 : keyMomentRows (202 : Fin 2886) =
    keyMomentRow202 := by decide +kernel

theorem keyMomentRowsAt203 : keyMomentRows (203 : Fin 2886) =
    keyMomentRow203 := by decide +kernel

theorem keyMomentRowsAt204 : keyMomentRows (204 : Fin 2886) =
    keyMomentRow204 := by decide +kernel

theorem keyMomentRowsAt205 : keyMomentRows (205 : Fin 2886) =
    keyMomentRow205 := by decide +kernel

theorem keyMomentRowsAt206 : keyMomentRows (206 : Fin 2886) =
    keyMomentRow206 := by decide +kernel

theorem keyMomentRowsAt207 : keyMomentRows (207 : Fin 2886) =
    keyMomentRow207 := by decide +kernel

theorem keyMomentRowsAt208 : keyMomentRows (208 : Fin 2886) =
    keyMomentRow208 := by decide +kernel

theorem keyMomentRowsAt209 : keyMomentRows (209 : Fin 2886) =
    keyMomentRow209 := by decide +kernel

theorem keyMomentRowsAt210 : keyMomentRows (210 : Fin 2886) =
    keyMomentRow210 := by decide +kernel

theorem keyMomentRowsAt211 : keyMomentRows (211 : Fin 2886) =
    keyMomentRow211 := by decide +kernel

theorem keyMomentRowsAt212 : keyMomentRows (212 : Fin 2886) =
    keyMomentRow212 := by decide +kernel

theorem keyMomentRowsAt213 : keyMomentRows (213 : Fin 2886) =
    keyMomentRow213 := by decide +kernel

theorem keyMomentRowsAt214 : keyMomentRows (214 : Fin 2886) =
    keyMomentRow214 := by decide +kernel

theorem keyMomentRowsAt215 : keyMomentRows (215 : Fin 2886) =
    keyMomentRow215 := by decide +kernel

theorem keyMomentRowsAt216 : keyMomentRows (216 : Fin 2886) =
    keyMomentRow216 := by decide +kernel

theorem keyMomentRowsAt217 : keyMomentRows (217 : Fin 2886) =
    keyMomentRow217 := by decide +kernel

theorem keyMomentRowsAt218 : keyMomentRows (218 : Fin 2886) =
    keyMomentRow218 := by decide +kernel

theorem keyMomentRowsAt219 : keyMomentRows (219 : Fin 2886) =
    keyMomentRow219 := by decide +kernel

theorem keyMomentRowsAt220 : keyMomentRows (220 : Fin 2886) =
    keyMomentRow220 := by decide +kernel

theorem keyMomentRowsAt221 : keyMomentRows (221 : Fin 2886) =
    keyMomentRow221 := by decide +kernel

theorem keyMomentRowsAt222 : keyMomentRows (222 : Fin 2886) =
    keyMomentRow222 := by decide +kernel

theorem keyMomentRowsAt223 : keyMomentRows (223 : Fin 2886) =
    keyMomentRow223 := by decide +kernel

theorem keyMomentChunkSound6 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 6) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 192 ∨ k.val = 193 ∨ k.val = 194 ∨ k.val = 195 ∨ k.val = 196 ∨ k.val = 197 ∨ k.val = 198 ∨ k.val = 199 ∨ k.val = 200 ∨ k.val = 201 ∨ k.val = 202 ∨ k.val = 203 ∨ k.val = 204 ∨ k.val = 205 ∨ k.val = 206 ∨ k.val = 207 ∨ k.val = 208 ∨ k.val = 209 ∨ k.val = 210 ∨ k.val = 211 ∨ k.val = 212 ∨ k.val = 213 ∨ k.val = 214 ∨ k.val = 215 ∨ k.val = 216 ∨ k.val = 217 ∨ k.val = 218 ∨ k.val = 219 ∨ k.val = 220 ∨ k.val = 221 ∨ k.val = 222 ∨ k.val = 223 := by omega
  rcases heq with h192 | h193 | h194 | h195 | h196 | h197 | h198 | h199 | h200 | h201 | h202 | h203 | h204 | h205 | h206 | h207 | h208 | h209 | h210 | h211 | h212 | h213 | h214 | h215 | h216 | h217 | h218 | h219 | h220 | h221 | h222 | h223
  · have he : k = (192 : Fin 2886) := Fin.ext h192
    subst k
    rw [keyMomentRowsAt192]
    exact keyMoment192 B hB
  · have he : k = (193 : Fin 2886) := Fin.ext h193
    subst k
    rw [keyMomentRowsAt193]
    exact keyMoment193 B hB
  · have he : k = (194 : Fin 2886) := Fin.ext h194
    subst k
    rw [keyMomentRowsAt194]
    exact keyMoment194 B hB
  · have he : k = (195 : Fin 2886) := Fin.ext h195
    subst k
    rw [keyMomentRowsAt195]
    exact keyMoment195 B hB
  · have he : k = (196 : Fin 2886) := Fin.ext h196
    subst k
    rw [keyMomentRowsAt196]
    exact keyMoment196 B hB
  · have he : k = (197 : Fin 2886) := Fin.ext h197
    subst k
    rw [keyMomentRowsAt197]
    exact keyMoment197 B hB
  · have he : k = (198 : Fin 2886) := Fin.ext h198
    subst k
    rw [keyMomentRowsAt198]
    exact keyMoment198 B hB
  · have he : k = (199 : Fin 2886) := Fin.ext h199
    subst k
    rw [keyMomentRowsAt199]
    exact keyMoment199 B hB
  · have he : k = (200 : Fin 2886) := Fin.ext h200
    subst k
    rw [keyMomentRowsAt200]
    exact keyMoment200 B hB
  · have he : k = (201 : Fin 2886) := Fin.ext h201
    subst k
    rw [keyMomentRowsAt201]
    exact keyMoment201 B hB
  · have he : k = (202 : Fin 2886) := Fin.ext h202
    subst k
    rw [keyMomentRowsAt202]
    exact keyMoment202 B hB
  · have he : k = (203 : Fin 2886) := Fin.ext h203
    subst k
    rw [keyMomentRowsAt203]
    exact keyMoment203 B hB
  · have he : k = (204 : Fin 2886) := Fin.ext h204
    subst k
    rw [keyMomentRowsAt204]
    exact keyMoment204 B hB
  · have he : k = (205 : Fin 2886) := Fin.ext h205
    subst k
    rw [keyMomentRowsAt205]
    exact keyMoment205 B hB
  · have he : k = (206 : Fin 2886) := Fin.ext h206
    subst k
    rw [keyMomentRowsAt206]
    exact keyMoment206 B hB
  · have he : k = (207 : Fin 2886) := Fin.ext h207
    subst k
    rw [keyMomentRowsAt207]
    exact keyMoment207 B hB
  · have he : k = (208 : Fin 2886) := Fin.ext h208
    subst k
    rw [keyMomentRowsAt208]
    exact keyMoment208 B hB
  · have he : k = (209 : Fin 2886) := Fin.ext h209
    subst k
    rw [keyMomentRowsAt209]
    exact keyMoment209 B hB
  · have he : k = (210 : Fin 2886) := Fin.ext h210
    subst k
    rw [keyMomentRowsAt210]
    exact keyMoment210 B hB
  · have he : k = (211 : Fin 2886) := Fin.ext h211
    subst k
    rw [keyMomentRowsAt211]
    exact keyMoment211 B hB
  · have he : k = (212 : Fin 2886) := Fin.ext h212
    subst k
    rw [keyMomentRowsAt212]
    exact keyMoment212 B hB
  · have he : k = (213 : Fin 2886) := Fin.ext h213
    subst k
    rw [keyMomentRowsAt213]
    exact keyMoment213 B hB
  · have he : k = (214 : Fin 2886) := Fin.ext h214
    subst k
    rw [keyMomentRowsAt214]
    exact keyMoment214 B hB
  · have he : k = (215 : Fin 2886) := Fin.ext h215
    subst k
    rw [keyMomentRowsAt215]
    exact keyMoment215 B hB
  · have he : k = (216 : Fin 2886) := Fin.ext h216
    subst k
    rw [keyMomentRowsAt216]
    exact keyMoment216 B hB
  · have he : k = (217 : Fin 2886) := Fin.ext h217
    subst k
    rw [keyMomentRowsAt217]
    exact keyMoment217 B hB
  · have he : k = (218 : Fin 2886) := Fin.ext h218
    subst k
    rw [keyMomentRowsAt218]
    exact keyMoment218 B hB
  · have he : k = (219 : Fin 2886) := Fin.ext h219
    subst k
    rw [keyMomentRowsAt219]
    exact keyMoment219 B hB
  · have he : k = (220 : Fin 2886) := Fin.ext h220
    subst k
    rw [keyMomentRowsAt220]
    exact keyMoment220 B hB
  · have he : k = (221 : Fin 2886) := Fin.ext h221
    subst k
    rw [keyMomentRowsAt221]
    exact keyMoment221 B hB
  · have he : k = (222 : Fin 2886) := Fin.ext h222
    subst k
    rw [keyMomentRowsAt222]
    exact keyMoment222 B hB
  · have he : k = (223 : Fin 2886) := Fin.ext h223
    subst k
    rw [keyMomentRowsAt223]
    exact keyMoment223 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
