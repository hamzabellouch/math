import OAI.Analysis.IrrationalRotation.Rotation.ParameterPositiveDiagonal
import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitEndpointLoss
import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitMarginalLaws

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem tendsto_projection_endpoint_bad_union_zero (hθ : Irrational θ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert)
    (hPm : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * p.measurableOperator θ hp * P = 0)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hbound : ∀ x, ‖F x‖ ≤ ‖P‖)
    (hmeas : ∀ v, StronglyMeasurable fun x => F x v)
    (hrep : ∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) :
    Tendsto (fun j : ℕ => (CircleCoupling.law p j).real
      ({ω | (inner ℂ PositiveDiagonalModel.e0
          (F (CircleCoupling.point p hr false ω) PositiveDiagonalModel.e0)).re <
            1 / (j : ℝ)} ∪
       {ω | 1 - (inner ℂ PositiveDiagonalModel.e0
          (F (CircleCoupling.point p hr true ω) PositiveDiagonalModel.e0)).re <
            1 / (j : ℝ)})) atTop (𝓝 0) := by
  let r : Circle → ℝ := fun x =>
    (inner ℂ PositiveDiagonalModel.e0 (F x PositiveDiagonalModel.e0)).re
  have hm : Measurable r :=
    ((Complex.continuous_re.comp
      (continuous_const.inner continuous_id)).comp_stronglyMeasurable
        (hmeas PositiveDiagonalModel.e0)).measurable
  have hi : ∀ᵐ x ∂(volume : Measure Circle), 0 < r x ∧ r x < 1 :=
    hp.ae_strict_diagonal_measurableOperator_of_nontrivial hθ P hPm hP hinv
      hP0 hP1 F hbound hmeas hrep
  exact (CircleCoupling.digitMarginalLaws hp hr).tendsto_endpoint_bad_union_zero
    hp (r := r) hm hi

end Invariant233.CircleParameterLaws

end

end OAI
