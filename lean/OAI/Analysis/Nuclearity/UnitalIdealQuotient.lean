import OAI.Analysis.JiangSu.Nonunital.ClosedIdealBasic

namespace OAI

/-! A local unital structure on the closed-ideal quotient. -/

noncomputable section

namespace WeakPureInfiniteness
open NonunitalClosedIdeal

variable {E : Type*} [CStarAlgebra E] (J : NonunitalClosedIdeal.Ideal E)

abbrev unitalIdealQuotientStructure : CStarAlgebra (QuotientAlgebra J) := by
  let _ : IsUnital (QuotientAlgebra J) := ⟨⟨QuotientAlgebra.mk J 1, fun x => by
    obtain ⟨y, rfl⟩ := QuotientAlgebra.mk_surjective J x
    constructor
    · rw [← QuotientAlgebra.mk_mul, one_mul]
    · rw [← QuotientAlgebra.mk_mul, mul_one]⟩⟩
  exact IsUnital.toCStarAlgebra

namespace UnitalIdealQuotient

local instance : CStarAlgebra (QuotientAlgebra J) := unitalIdealQuotientStructure J

theorem mk_one : QuotientAlgebra.mk J 1 = 1 := by
  have he : QuotientAlgebra.mk J 1 * (1 : QuotientAlgebra J) = 1 := by
    obtain ⟨x, hx⟩ := QuotientAlgebra.mk_surjective J (1 : QuotientAlgebra J)
    rw [← hx, ← QuotientAlgebra.mk_mul, one_mul]
  simpa only [mul_one] using he

def quotientHom : E →⋆ₐ[ℂ] QuotientAlgebra J :=
  { QuotientAlgebra.mkHom J with
    map_one' := mk_one J
    commutes' := fun c => by
      rw [Algebra.algebraMap_eq_smul_one]
      change QuotientAlgebra.mk J (c • (1 : E)) = _
      rw [QuotientAlgebra.mk_smul, mk_one, Algebra.algebraMap_eq_smul_one] }

theorem quotientHom_eq_zero_iff (x : E) : quotientHom J x = 0 ↔ x ∈ J.module := by
  change QuotientAlgebra.mk J x = QuotientAlgebra.mk J 0 ↔ _
  simpa only [sub_zero] using QuotientAlgebra.mk_eq_mk_iff J x 0

end UnitalIdealQuotient
end WeakPureInfiniteness

end

end OAI
