import OAI.GroupTheory.PolycyclicRecognition.Algebra.ComplexDerivationDescent
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexifiedOperatorExponential

namespace OAI

/-! # Real derivation logarithms of powers of semisimple Lie automorphisms -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

theorem real_semisimple_lie_automorphism_has_power_log (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : LieDerivation ℝ L L,
      (NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap)).toLinearMap =
        S.toLinearMap ^ m := by
  let : ComplexNormedLieAlgebra (ℂ ⊗[ℝ] L) := complexificationNormedLie L
  let CS := complexifiedLieEquiv L S
  have hCS : Module.End.IsSemisimple CS.toLinearMap :=
    complexifiedLieEquiv_semisimple L S hS
  obtain ⟨m, hm, D, he, hc⟩ := semisimple_real_form_has_power_log CS hCS
    (complexificationConjSemilinear L) (complexifiedLieEquiv_conj L S)
  refine ⟨m, hm, complexDerivationRealPart L D, ?_⟩
  apply realEnd_baseChange_injective L
  change ((NormedSpace.exp (LinearMap.toContinuousLinearMap
      (complexDerivationRealPart L D).toLinearMap)).toLinearMap).baseChange ℂ =
    (S.toLinearMap ^ m).baseChange ℂ
  rw [complexifiedEnd_exp, complexDerivationRealPart_baseChange L D hc, he,
    LinearMap.baseChange_pow]
  rfl

end PolycyclicRecognition

end

end OAI
