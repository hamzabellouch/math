import OAI.Geometry.SurfaceImmersion.Correction.SmoothedMetricStep

namespace OAI

/-! The full one-step defect bound with the constructed coordinate smoother. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.ExactCorrection
open FiniteOrderSmoothing WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Substituting the actual smoothing estimates into the metric identity
keeps the dependence on both uncontrolled higher input norms linear. -/
theorem smoothed_metric_step_bound (r m : ℕ)
    {target : Base → ℝ} (htarget : ContDiff ℝ ∞ target)
    {G U : Base → V} (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
    (hU : ContDiff ℝ ∞ U) (v w : Base)
    {s t τ δ δ' BH CH BG CG D BE : ℝ}
    (hτ : 0 < τ) (hτs : τ ≤ s) (hst : s ≤ t) (hδ : δ ≠ 0) (hδ' : δ' ≠ 0)
    (hHc : HasCompactSupport (normalizedMetricDefect target δ G v w))
    (hbH : WeightedBound Set.univ t r BH (normalizedMetricDefect target δ G v w))
    (hcH : WeightedBound Set.univ t m CH (normalizedMetricDefect target δ G v w))
    (hbG : WeightedBound Set.univ t r BG (fderiv ℝ G))
    (hcG : WeightedBound Set.univ t m CG (fderiv ℝ G))
    (hbU : WeightedBound Set.univ τ m D (fderiv ℝ U))
    (hbE : WeightedBound Set.univ τ m BE
      (realizedMetricError target (finiteSmooth r s (normalizedMetricDefect target δ G v w))
        δ δ' (finiteSmooth r s G) U v w)) :
    WeightedBound Set.univ τ m
      ((δ' ^ 2)⁻¹ *
        (δ ^ 2 * (tailConstant r * (BH * (s / t) ^ r + CH * (τ / t) ^ r)) + BE +
          2 * ‖v‖ * ‖w‖ * (2 ^ m *
            (tailConstant r * (BG * (s / t) ^ r + CG * (τ / t) ^ r)) * D)))
      (normalizedMetricDefect target δ' (G + U) v w - target) := by
  have hs : 0 < s := hτ.trans_le hτs
  have hH := contDiff_normalizedMetricDefect htarget δ hG v w
  exact normalized_metric_step_bound htarget (finiteSmooth_smooth r hs hH)
    hδ hδ' hτ.le m hG (finiteSmooth_smooth r hs hG) hU v w
    (weighted_smoothing_tail r m hτ hτs hst hH hHc hbH hcH) hbE
    (weighted_smoothing_metricCrossTerm r m hτ hτs hst hG hGc hU hbG hcG hbU v w)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
