import OAI.Analysis.IrrationalRotation.Operators.DenseOperatorRange
import OAI.Analysis.IrrationalRotation.Rotation.RotationMeasurableLaws
import OAI.Analysis.IrrationalRotation.Model.ParameterCircleOperator

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.Rotation

theorem measurableRepresentation_injective_of_ae_ne_zero
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (hne : ∀ᵐ x ∂circleMeasure, g x ≠ 0) :
    Function.Injective (measurableRepresentation θ g C hC hg hb) := by
  have horbit : ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, g (action θ k x) ≠ 0 := by
    apply ae_all_iff.mpr
    intro k
    exact (action_measurePreserving θ k).quasiMeasurePreserving.ae
      (p := fun x => g x ≠ 0) hne
  intro ξ η hξη
  apply Lp.ext
  filter_upwards [measurableRepresentation_coordinates_ae θ g C hC hg hb ξ,
    measurableRepresentation_coordinates_ae θ g C hC hg hb η, horbit]
    with x hξ hη hx
  apply lp.ext
  funext k
  apply mul_left_cancel₀ (hx k)
  rw [← hξ k, ← hη k, hξη]

theorem measurableRepresentation_denseRange_of_ae_ne_zero
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (hne : ∀ᵐ x ∂circleMeasure, g x ≠ 0) :
    DenseRange (measurableRepresentation θ g C hC hg hb) := by
  apply OperatorRange.denseRange_of_adjoint_injective
  rw [← measurableRepresentation_star]
  apply measurableRepresentation_injective_of_ae_ne_zero
  filter_upwards [hne] with x hx
  exact star_ne_zero.mpr hx

theorem U_mul_measurableRepresentation_injective_of_ae_ne_zero
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (hne : ∀ᵐ x ∂circleMeasure, g x ≠ 0) :
    Function.Injective (U * measurableRepresentation θ g C hC hg hb) :=
  (OperatorRange.unitary_injective U U_mem_unitary).comp
    (measurableRepresentation_injective_of_ae_ne_zero θ g C hC hg hb hne)

theorem U_mul_measurableRepresentation_denseRange_of_ae_ne_zero
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (hne : ∀ᵐ x ∂circleMeasure, g x ≠ 0) :
    DenseRange (U * measurableRepresentation θ g C hC hg hb) :=
  (OperatorRange.unitary_surjective U U_mem_unitary).denseRange.comp
    (measurableRepresentation_denseRange_of_ae_ne_zero θ g C hC hg hb hne) U.continuous

end Invariant233.Rotation

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem measurableOperator_injective : Function.Injective (p.measurableOperator θ hp) := by
  apply Rotation.U_mul_measurableRepresentation_injective_of_ae_ne_zero
  exact Filter.Eventually.of_forall fun x => Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'

theorem measurableOperator_denseRange : DenseRange (p.measurableOperator θ hp) := by
  apply Rotation.U_mul_measurableRepresentation_denseRange_of_ae_ne_zero
  exact Filter.Eventually.of_forall fun x => Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'

end Invariant233.CircleParameterLaws

end

end OAI
