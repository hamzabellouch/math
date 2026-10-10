import OAI.Analysis.FiniteFactor.CrossedProduct.ProjectionErrors

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceTruncatedCoefficient_measurable (θ : SourceCoordinate → ℝ)
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (j : ℕ) (n : ℤ) :
    Measurable (sourceTruncatedCoefficient θ p j n) := by
  unfold sourceTruncatedCoefficient laurentProductCoefficient
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro k _
  split_ifs
  · exact ((sourceProjectionLeftCoefficient_measurable θ p _).comp (sourceBiasedEndpoint_measurable _)).mul
      ((sourceProjectionRightCoefficient_measurable θ p _).comp (sourceBiasedEndpoint_measurable _))
  · exact measurable_const

/-- Each actual truncated coefficient has norm at most one under the full
biased law. This follows from the original absolute convolution bound. -/
theorem sourceTruncatedCoefficient_norm_le_one (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j n : ℕ) : ∀ᵐ ω ∂sourceBiasedLaw j, ‖sourceTruncatedCoefficient θ p j n ω‖ ≤ 1 := by
  filter_upwards [sourceProjection_convolution θ hθ hs hp hproj hinv j] with ω hc
  unfold sourceTruncatedCoefficient
  rw [laurent_coefficient_eq_finite_convolution]
  apply (norm_sum_le _ _).trans
  apply ((hc n).2.1.sum_le_tsum _ (fun k _ => norm_nonneg _)).trans
  exact (hc n).2.2

theorem sourceTruncatedCoefficient_integrable (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j n : ℕ) : Integrable (sourceTruncatedCoefficient θ p j n) (sourceBiasedLaw j) :=
  (integrable_const (1 : ℝ)).mono' (sourceTruncatedCoefficient_measurable θ p j n).aestronglyMeasurable
    (sourceTruncatedCoefficient_norm_le_one θ hθ hs hp hproj hinv j n)

end
end FiniteFactor

end OAI
