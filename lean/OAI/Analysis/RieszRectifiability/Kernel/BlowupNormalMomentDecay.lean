import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.BlowupNormalMoments
import OAI.Analysis.RieszRectifiability.Foundations.ShrinkingBallIntegrals

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem blowup_positiveNormalHeight_moments_tendsto_zero {d : ℕ}
    (n : ℕ) (hn : 0 < n) (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (G : ℝ) (hg : GlobalUpperGrowth n G μ) (e : Ambient d)
    (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hi : IntegrableOn (positiveNormalPotential n e) (ball (0 : Ambient d) R₀) μ)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0))
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun j => ∫ x in ball (0 : Ambient d) R,
      positiveNormalHeight e x ∂blowupMeasure n μ 0 (r j)) atTop (𝓝 0) := by
  have hscale : Tendsto (fun j => r j * R) atTop (𝓝 0) := by
    simpa only [zero_mul] using! hr0.mul_const R
  have hpot := local_integral_tendsto_zero_on_shrinking_balls μ (positiveNormalPotential n e)
    0 R₀ hR₀ hi (fun j => r j * R) hscale
      (measure_ball_tendsto_zero_of_growth n hn μ G hg 0 (fun j => r j * R)
        (fun j => mul_pos (hr j) hR) hscale)
  have hbound : ∀ᶠ j in atTop,
      (∫ x in ball (0 : Ambient d) R, positiveNormalHeight e x ∂blowupMeasure n μ 0 (r j)) ≤
        R ^ (n + 1) * ∫ y in ball (0 : Ambient d) (r j * R), positiveNormalPotential n e y ∂μ := by
    filter_upwards [hscale.eventually (gt_mem_nhds hR₀)] with j hj
    exact blowup_positiveNormalHeight_le_potential_integral n μ e (r j) R (hr j) hR
      (hi.mono_set (ball_subset_ball hj.le))
  have hright : Tendsto (fun j => R ^ (n + 1) *
      ∫ y in ball (0 : Ambient d) (r j * R), positiveNormalPotential n e y ∂μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using! hpot.const_mul (R ^ (n + 1))
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ =>
    integral_nonneg (positiveNormalHeight_nonneg e)) hbound hright

end

end RieszRectifiability

end OAI
