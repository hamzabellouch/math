import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound5
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt160 : keyMomentRows (160 : Fin 2886) =
    keyMomentRow160 := by decide +kernel

theorem keyMomentRowsAt161 : keyMomentRows (161 : Fin 2886) =
    keyMomentRow161 := by decide +kernel

theorem keyMomentRowsAt162 : keyMomentRows (162 : Fin 2886) =
    keyMomentRow162 := by decide +kernel

theorem keyMomentRowsAt163 : keyMomentRows (163 : Fin 2886) =
    keyMomentRow163 := by decide +kernel

theorem keyMomentRowsAt164 : keyMomentRows (164 : Fin 2886) =
    keyMomentRow164 := by decide +kernel

theorem keyMomentRowsAt165 : keyMomentRows (165 : Fin 2886) =
    keyMomentRow165 := by decide +kernel

theorem keyMomentRowsAt166 : keyMomentRows (166 : Fin 2886) =
    keyMomentRow166 := by decide +kernel

theorem keyMomentRowsAt167 : keyMomentRows (167 : Fin 2886) =
    keyMomentRow167 := by decide +kernel

theorem keyMomentRowsAt168 : keyMomentRows (168 : Fin 2886) =
    keyMomentRow168 := by decide +kernel

theorem keyMomentRowsAt169 : keyMomentRows (169 : Fin 2886) =
    keyMomentRow169 := by decide +kernel

theorem keyMomentRowsAt170 : keyMomentRows (170 : Fin 2886) =
    keyMomentRow170 := by decide +kernel

theorem keyMomentRowsAt171 : keyMomentRows (171 : Fin 2886) =
    keyMomentRow171 := by decide +kernel

theorem keyMomentRowsAt172 : keyMomentRows (172 : Fin 2886) =
    keyMomentRow172 := by decide +kernel

theorem keyMomentRowsAt173 : keyMomentRows (173 : Fin 2886) =
    keyMomentRow173 := by decide +kernel

theorem keyMomentRowsAt174 : keyMomentRows (174 : Fin 2886) =
    keyMomentRow174 := by decide +kernel

theorem keyMomentRowsAt175 : keyMomentRows (175 : Fin 2886) =
    keyMomentRow175 := by decide +kernel

theorem keyMomentRowsAt176 : keyMomentRows (176 : Fin 2886) =
    keyMomentRow176 := by decide +kernel

theorem keyMomentRowsAt177 : keyMomentRows (177 : Fin 2886) =
    keyMomentRow177 := by decide +kernel

theorem keyMomentRowsAt178 : keyMomentRows (178 : Fin 2886) =
    keyMomentRow178 := by decide +kernel

theorem keyMomentRowsAt179 : keyMomentRows (179 : Fin 2886) =
    keyMomentRow179 := by decide +kernel

theorem keyMomentRowsAt180 : keyMomentRows (180 : Fin 2886) =
    keyMomentRow180 := by decide +kernel

theorem keyMomentRowsAt181 : keyMomentRows (181 : Fin 2886) =
    keyMomentRow181 := by decide +kernel

theorem keyMomentRowsAt182 : keyMomentRows (182 : Fin 2886) =
    keyMomentRow182 := by decide +kernel

theorem keyMomentRowsAt183 : keyMomentRows (183 : Fin 2886) =
    keyMomentRow183 := by decide +kernel

theorem keyMomentRowsAt184 : keyMomentRows (184 : Fin 2886) =
    keyMomentRow184 := by decide +kernel

theorem keyMomentRowsAt185 : keyMomentRows (185 : Fin 2886) =
    keyMomentRow185 := by decide +kernel

theorem keyMomentRowsAt186 : keyMomentRows (186 : Fin 2886) =
    keyMomentRow186 := by decide +kernel

theorem keyMomentRowsAt187 : keyMomentRows (187 : Fin 2886) =
    keyMomentRow187 := by decide +kernel

theorem keyMomentRowsAt188 : keyMomentRows (188 : Fin 2886) =
    keyMomentRow188 := by decide +kernel

theorem keyMomentRowsAt189 : keyMomentRows (189 : Fin 2886) =
    keyMomentRow189 := by decide +kernel

theorem keyMomentRowsAt190 : keyMomentRows (190 : Fin 2886) =
    keyMomentRow190 := by decide +kernel

theorem keyMomentRowsAt191 : keyMomentRows (191 : Fin 2886) =
    keyMomentRow191 := by decide +kernel

theorem keyMomentChunkSound5 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 5) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 160 ∨ k.val = 161 ∨ k.val = 162 ∨ k.val = 163 ∨ k.val = 164 ∨ k.val = 165 ∨ k.val = 166 ∨ k.val = 167 ∨ k.val = 168 ∨ k.val = 169 ∨ k.val = 170 ∨ k.val = 171 ∨ k.val = 172 ∨ k.val = 173 ∨ k.val = 174 ∨ k.val = 175 ∨ k.val = 176 ∨ k.val = 177 ∨ k.val = 178 ∨ k.val = 179 ∨ k.val = 180 ∨ k.val = 181 ∨ k.val = 182 ∨ k.val = 183 ∨ k.val = 184 ∨ k.val = 185 ∨ k.val = 186 ∨ k.val = 187 ∨ k.val = 188 ∨ k.val = 189 ∨ k.val = 190 ∨ k.val = 191 := by omega
  rcases heq with h160 | h161 | h162 | h163 | h164 | h165 | h166 | h167 | h168 | h169 | h170 | h171 | h172 | h173 | h174 | h175 | h176 | h177 | h178 | h179 | h180 | h181 | h182 | h183 | h184 | h185 | h186 | h187 | h188 | h189 | h190 | h191
  · have he : k = (160 : Fin 2886) := Fin.ext h160
    subst k
    rw [keyMomentRowsAt160]
    exact keyMoment160 B hB
  · have he : k = (161 : Fin 2886) := Fin.ext h161
    subst k
    rw [keyMomentRowsAt161]
    exact keyMoment161 B hB
  · have he : k = (162 : Fin 2886) := Fin.ext h162
    subst k
    rw [keyMomentRowsAt162]
    exact keyMoment162 B hB
  · have he : k = (163 : Fin 2886) := Fin.ext h163
    subst k
    rw [keyMomentRowsAt163]
    exact keyMoment163 B hB
  · have he : k = (164 : Fin 2886) := Fin.ext h164
    subst k
    rw [keyMomentRowsAt164]
    exact keyMoment164 B hB
  · have he : k = (165 : Fin 2886) := Fin.ext h165
    subst k
    rw [keyMomentRowsAt165]
    exact keyMoment165 B hB
  · have he : k = (166 : Fin 2886) := Fin.ext h166
    subst k
    rw [keyMomentRowsAt166]
    exact keyMoment166 B hB
  · have he : k = (167 : Fin 2886) := Fin.ext h167
    subst k
    rw [keyMomentRowsAt167]
    exact keyMoment167 B hB
  · have he : k = (168 : Fin 2886) := Fin.ext h168
    subst k
    rw [keyMomentRowsAt168]
    exact keyMoment168 B hB
  · have he : k = (169 : Fin 2886) := Fin.ext h169
    subst k
    rw [keyMomentRowsAt169]
    exact keyMoment169 B hB
  · have he : k = (170 : Fin 2886) := Fin.ext h170
    subst k
    rw [keyMomentRowsAt170]
    exact keyMoment170 B hB
  · have he : k = (171 : Fin 2886) := Fin.ext h171
    subst k
    rw [keyMomentRowsAt171]
    exact keyMoment171 B hB
  · have he : k = (172 : Fin 2886) := Fin.ext h172
    subst k
    rw [keyMomentRowsAt172]
    exact keyMoment172 B hB
  · have he : k = (173 : Fin 2886) := Fin.ext h173
    subst k
    rw [keyMomentRowsAt173]
    exact keyMoment173 B hB
  · have he : k = (174 : Fin 2886) := Fin.ext h174
    subst k
    rw [keyMomentRowsAt174]
    exact keyMoment174 B hB
  · have he : k = (175 : Fin 2886) := Fin.ext h175
    subst k
    rw [keyMomentRowsAt175]
    exact keyMoment175 B hB
  · have he : k = (176 : Fin 2886) := Fin.ext h176
    subst k
    rw [keyMomentRowsAt176]
    exact keyMoment176 B hB
  · have he : k = (177 : Fin 2886) := Fin.ext h177
    subst k
    rw [keyMomentRowsAt177]
    exact keyMoment177 B hB
  · have he : k = (178 : Fin 2886) := Fin.ext h178
    subst k
    rw [keyMomentRowsAt178]
    exact keyMoment178 B hB
  · have he : k = (179 : Fin 2886) := Fin.ext h179
    subst k
    rw [keyMomentRowsAt179]
    exact keyMoment179 B hB
  · have he : k = (180 : Fin 2886) := Fin.ext h180
    subst k
    rw [keyMomentRowsAt180]
    exact keyMoment180 B hB
  · have he : k = (181 : Fin 2886) := Fin.ext h181
    subst k
    rw [keyMomentRowsAt181]
    exact keyMoment181 B hB
  · have he : k = (182 : Fin 2886) := Fin.ext h182
    subst k
    rw [keyMomentRowsAt182]
    exact keyMoment182 B hB
  · have he : k = (183 : Fin 2886) := Fin.ext h183
    subst k
    rw [keyMomentRowsAt183]
    exact keyMoment183 B hB
  · have he : k = (184 : Fin 2886) := Fin.ext h184
    subst k
    rw [keyMomentRowsAt184]
    exact keyMoment184 B hB
  · have he : k = (185 : Fin 2886) := Fin.ext h185
    subst k
    rw [keyMomentRowsAt185]
    exact keyMoment185 B hB
  · have he : k = (186 : Fin 2886) := Fin.ext h186
    subst k
    rw [keyMomentRowsAt186]
    exact keyMoment186 B hB
  · have he : k = (187 : Fin 2886) := Fin.ext h187
    subst k
    rw [keyMomentRowsAt187]
    exact keyMoment187 B hB
  · have he : k = (188 : Fin 2886) := Fin.ext h188
    subst k
    rw [keyMomentRowsAt188]
    exact keyMoment188 B hB
  · have he : k = (189 : Fin 2886) := Fin.ext h189
    subst k
    rw [keyMomentRowsAt189]
    exact keyMoment189 B hB
  · have he : k = (190 : Fin 2886) := Fin.ext h190
    subst k
    rw [keyMomentRowsAt190]
    exact keyMoment190 B hB
  · have he : k = (191 : Fin 2886) := Fin.ext h191
    subst k
    rw [keyMomentRowsAt191]
    exact keyMoment191 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
