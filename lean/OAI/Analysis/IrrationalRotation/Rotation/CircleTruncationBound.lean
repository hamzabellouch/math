import OAI.Analysis.IrrationalRotation.Model.CircleTruncation
import OAI.Analysis.IrrationalRotation.Rotation.CircleTruncationMass
import OAI.Analysis.IrrationalRotation.Rotation.CircleTruncationIntegral
import OAI.Analysis.IrrationalRotation.Rotation.ParameterPositiveDiagonal

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace
namespace Invariant233.CircleCoupling

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem truncationBounds_of_diagonal_interior
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hFm : StronglyMeasurable (fun x => F x (lp.single 2 0 1)))
    (hF : ∀ x, IsStarProjection (F x))
    (hri : ∀ᵐ x ∂volume, 0 < projectionDiagonal F x ∧ projectionDiagonal F x < 1) :
    TruncationBounds θ p hr F := by
  have hrm : Measurable (projectionDiagonal F) :=
    Complex.continuous_re.measurable.comp
      (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp_stronglyMeasurable hFm).measurable)
  obtain ⟨J, hJ, hmass⟩ := exists_truncationEvent_mass_threshold hp hr hrm hri
  refine ⟨J, hJ, fun j hj => ⟨hmass j hj, ?_⟩⟩
  have hjpos : 1 ≤ j := hJ.trans hj
  have hint : p.ε j * (law p j).real (truncationEvent p j hr (projectionDiagonal F)) ≤
      ∫ ω in truncationEvent p j hr (projectionDiagonal F),
        truncationSum θ p j hr F ω ∂law p j := by
    exact truncationEvent_integral_lower hp j hjpos hr F hFm hF
  calc
    (Real.exp (-90) / 2) * p.ε j ≤
        p.ε j * (law p j).real (truncationEvent p j hr (projectionDiagonal F)) := by
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right (hmass j hj) (hp.epsilon_pos j hjpos).le
    _ ≤ _ := hint

end Invariant233.CircleCoupling

namespace Invariant233.CircleParameterLaws

theorem exists_rational_graph_field_with_truncation_bounds
    {θ : ℝ} (hθ : Irrational θ) {p : CircleParameterData}
    (hp : CircleParameterLaws θ p)
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hmem : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (htrace0 : 0 < (Rotation.vacuumFunctional P).re)
    (htrace1 : (Rotation.vacuumFunctional P).re < 1)
    (hinv : (1 - P) * p.measurableOperator θ hp * P = 0) :
    ∃ hr : ∀ i, 0 < MixedRadix.radices p.q i,
      ∃ F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber,
        (∀ x, IsStarProjection (F x)) ∧
        (∀ x, ‖F x‖ ≤ ‖P‖) ∧
        (∀ v : Rotation.Fiber, StronglyMeasurable fun x => F x v) ∧
        (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
        p.RationalGraphIdentities θ F ∧ CircleCoupling.TruncationBounds θ p hr F := by
  obtain ⟨F, hF, hbound, hmeas, hrep, hgraph⟩ :=
    hp.exists_rational_graph_field hmem hP hinv
  let hr := MixedRadix.radices_pos hp.q_pos hp.frequency_increasing hp.frequency_divisible
  refine ⟨hr, F, hF, hbound, hmeas, hrep, hgraph, ?_⟩
  apply CircleCoupling.truncationBounds_of_diagonal_interior hp hr F
    (hmeas (lp.single 2 0 1)) hF
  have hri := hp.ae_strict_diagonal_measurableOperator hθ P hmem hP hinv
    htrace0 htrace1 F hbound hmeas hrep
  simpa [CircleCoupling.projectionDiagonal, PositiveDiagonalModel.e0,
    lp.inner_single_left, circleMeasure] using hri

end Invariant233.CircleParameterLaws

end

end OAI
