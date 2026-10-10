import OAI.Analysis.OperatorAlgebra.AntiunitaryCPConjugation

namespace OAI

/-! Multiplication and adjoints under an actual involutive antiunitary. -/
noncomputable section
open scoped InnerProductSpace ComplexConjugate
namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma antiunitaryConjugate_mul (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (a b : H →L[ℂ] H) :
    antiunitaryConjugate J (a * b) = antiunitaryConjugate J a * antiunitaryConjugate J b := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [antiunitaryConjugate_apply, mul_apply_eq_comp]
  rw [hJ (b (J x))]

lemma antiunitaryConjugate_star (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (a : H →L[ℂ] H) :
    antiunitaryConjugate J (star a) = star (antiunitaryConjugate J a) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (J (star a (J x))) y = inner ℂ x (J (a (J y)))
  calc
    _ = star (inner ℂ (star a (J x)) (J y)) := by
      conv_lhs => rw [← hJ y]
      exact BoundedRecovery.antiunitary_inner J _ _
    _ = star (inner ℂ (J x) (a (J y))) :=
      congrArg star (ContinuousLinearMap.adjoint_inner_left a (J y) (J x))
    _ = _ := by
      have h := BoundedRecovery.antiunitary_inner J (J x) (a (J y))
      simpa only [hJ x] using h.symm

lemma antiunitaryConjugate_isStarProjection (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    IsStarProjection (antiunitaryConjugate J p) where
  isSelfAdjoint := by
    change star (antiunitaryConjugate J p) = antiunitaryConjugate J p
    rw [← antiunitaryConjugate_star J hJ, hp.isSelfAdjoint.star_eq]
  isIdempotentElem := by
    change antiunitaryConjugate J p * antiunitaryConjugate J p = antiunitaryConjugate J p
    rw [← antiunitaryConjugate_mul J hJ]
    exact congrArg (antiunitaryConjugate J) hp.isIdempotentElem

end WeakPureInfiniteness

end

end OAI
