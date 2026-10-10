import OAI.Analysis.LipschitzHilbert.Trees.SourceCountParameters
import OAI.Analysis.LipschitzHilbert.Fourier.FourierAveragingScale

namespace OAI

/-! Constructed near-uniform averaging at the actual rounded source scale. -/

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace LipschitzHilbert

open PhaseCombinatorics

theorem source_step_tendsto_atTop : Tendsto SourceParameters.step atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ ((Real.tendsto_exp_atTop).comp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  have h := Real.exp_le_exp.mpr (SourceParameters.log_step_bounds hL).1
  simpa only [Function.comp_apply, Real.exp_log (SourceParameters.step_pos L)] using h

/-- At every sufficiently large source parameter and every finite line
interval, the Fourier-gap averaging law is an actual convex mixture
of the uniform interval law and a probability remainder. -/
theorem exists_source_averaging_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ L : ℝ in atTop, ∀ a b : ℝ, a < b →
      ∃ (eta : ℝ) (remainder : Measure ℝ),
        0 < eta ∧ eta ≤ C * SourceParameters.step L ^ (-(1 / 16 : ℝ)) ∧
        eta < 1 / 2 ∧ IsProbabilityMeasure remainder ∧
        FourierGap (predictionMixture (intervalProbability a b) remainder eta)
          (1 / ((b - a) * SourceParameters.step L ^ (-(1 / 8 : ℝ)))) := by
  obtain ⟨C, hC, haverage⟩ := exists_power_scale_averaging_constant
  refine ⟨C, hC, ?_⟩
  have hdecay : Tendsto (fun L => C * SourceParameters.step L ^ (-(1 / 16 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (tendsto_const_nhds (x := C)).mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp
        source_step_tendsto_atTop)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with L hL hsmall
  intro a b hab
  exact haverage a b (SourceParameters.step L) hab
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hsmall

end LipschitzHilbert

end

end OAI
