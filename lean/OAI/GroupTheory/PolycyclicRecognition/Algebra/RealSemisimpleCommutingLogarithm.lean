import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealSemisimpleLieLogarithm

namespace OAI

/-! # The real semisimple logarithm commutes with the commutant -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

theorem real_semisimple_lie_automorphism_has_commuting_power_log (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : LieDerivation ℝ L L,
      (NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap)).toLinearMap =
        S.toLinearMap ^ m ∧
        ∀ T : Module.End ℝ L, Commute S.toLinearMap T → Commute D.toLinearMap T := by
  let : ComplexNormedLieAlgebra (ℂ ⊗[ℝ] L) := complexificationNormedLie L
  let CS := complexifiedLieEquiv L S
  have hCS : Module.End.IsSemisimple CS.toLinearMap :=
    complexifiedLieEquiv_semisimple L S hS
  obtain ⟨m, hm, D, he, hc, hcomm⟩ := semisimple_real_form_has_commuting_power_log CS hCS
    (complexificationConjSemilinear L) (complexifiedLieEquiv_conj L S)
  refine ⟨m, hm, complexDerivationRealPart L D, ?_, ?_⟩
  · apply realEnd_baseChange_injective L
    change ((NormedSpace.exp (LinearMap.toContinuousLinearMap
        (complexDerivationRealPart L D).toLinearMap)).toLinearMap).baseChange ℂ =
      (S.toLinearMap ^ m).baseChange ℂ
    rw [complexifiedEnd_exp, complexDerivationRealPart_baseChange L D hc, he,
      LinearMap.baseChange_pow]
    rfl
  · intro T hT
    let f := Module.End.baseChangeHom ℝ ℂ L
    have ht : Commute D.toLinearMap (T.baseChange ℂ) := hcomm _ (hT.map f)
    change (complexDerivationRealPart L D).toLinearMap * T =
      T * (complexDerivationRealPart L D).toLinearMap
    apply realEnd_baseChange_injective L
    change f ((complexDerivationRealPart L D).toLinearMap * T) =
      f (T * (complexDerivationRealPart L D).toLinearMap)
    simp only [map_mul]
    change (complexDerivationRealPart L D).toLinearMap.baseChange ℂ * T.baseChange ℂ =
      T.baseChange ℂ * (complexDerivationRealPart L D).toLinearMap.baseChange ℂ
    rw [complexDerivationRealPart_baseChange L D hc]
    exact ht.eq

end PolycyclicRecognition

end

end OAI
