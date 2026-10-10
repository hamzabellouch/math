import OAI.NumberTheory.DukePrimeDegree.Entropy.RootInformationScale
import Mathlib.MeasureTheory.Covering.Besicovitch

namespace OAI

/-!
# Linear lower bounds at typical centers of real leaf measures

Differentiation of Lebesgue measure relative to an arbitrary locally
finite real measure bounds their small-ball ratio at almost every center.
This supplies the dimension-one bound for actual root information.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace DukePrimeDegree

/-- A locally finite measure has at least linear mass in small balls
around almost every one of its own typical points. -/
theorem ae_real_ball_linear_lower_bound (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    ∀ᵐ x ∂ν, ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ᶠ r : ℝ in 𝓝[>] 0, ENNReal.ofReal r ≤ C * ν (ball x r) := by
  have hhalf : Tendsto (fun r : ℝ => r / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun r : ℝ => r / 2) := continuous_id.div_const 2
      simpa only [zero_div] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < r / 2
      exact div_pos (show 0 < r from hr) (by norm_num)
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv (volume : Measure ℝ) ν,
    Measure.rnDeriv_lt_top (volume : Measure ℝ) ν] with x hx hfin
  let C := (volume : Measure ℝ).rnDeriv ν x + 1
  have hC : C ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hfin.ne, ENNReal.one_ne_top⟩
  have hC0 : C ≠ 0 := by dsimp [C]; positivity
  have hless : (volume : Measure ℝ).rnDeriv ν x < C := ENNReal.lt_add_right hfin.ne one_ne_zero
  have hbound := (hx.comp hhalf).eventually (gt_mem_nhds hless)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, self_mem_nhdsWithin] with r hr hr0
  change 0 < r at hr0
  have h := (ENNReal.div_le_iff_le_mul (Or.inr hC) (Or.inr hC0)).mp hr.le
  have hs : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  have hvol : (volume : Measure ℝ) (closedBall x (r / 2)) = ENNReal.ofReal r := by
    rw [Real.volume_closedBall]
    congr 1
    ring
  rw [hvol] at h
  exact h.trans (by simpa only [mul_comm] using
    (mul_le_mul_left (measure_mono hs : ν (closedBall x (r / 2)) ≤ ν (ball x r)) C))

end DukePrimeDegree

end

end OAI
