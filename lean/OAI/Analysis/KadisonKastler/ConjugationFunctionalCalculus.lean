import OAI.Analysis.KadisonKastler.ConjugateRightAlgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

namespace OAI

/-! # Real functional calculus under an antiunitary conjugation -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An involutive antiunitary acts by a real star-algebra automorphism. -/
def conjugationRealStarAlgEquiv (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) :
    (H →L[ℂ] H) ≃⋆ₐ[ℝ] (H →L[ℂ] H) where
  toFun := conjugationOperator J
  invFun := conjugationOperator J
  left_inv := conjugationOperator_twice J hJ
  right_inv := conjugationOperator_twice J hJ
  map_add' := conjugationOperator_add J
  map_mul' := conjugationOperator_mul J hJ
  map_smul' r a := by
    change conjugationOperator J ((r : ℂ) • a) = (r : ℂ) • conjugationOperator J a
    rw [conjugationOperator_smul]
    simp
  map_star' := conjugationOperator_star J hJ

theorem conjugationRealStarAlgEquiv_isometry (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) : Isometry (conjugationRealStarAlgEquiv J hJ) := by
  apply Isometry.of_dist_eq
  intro a b
  rw [dist_eq_norm, dist_eq_norm]
  change ‖conjugationOperator J a - conjugationOperator J b‖ = ‖a - b‖
  exact norm_conjugationOperator_sub J hJ a b

theorem conjugationOperator_selfAdjoint (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (conjugationOperator J A) := by
  change star (conjugationOperator J A) = conjugationOperator J A
  rw [← conjugationOperator_star J hJ, hA.star_eq]

theorem conjugationOperator_cfc_real (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ A)) :
    conjugationOperator J (cfc f A) = cfc f (conjugationOperator J A) :=
  (conjugationRealStarAlgEquiv J hJ).toStarAlgHom.map_cfc f A hf
    (conjugationRealStarAlgEquiv_isometry J hJ).continuous hA
    (conjugationOperator_selfAdjoint J hJ hA)

end

end KadisonKastler

end OAI
