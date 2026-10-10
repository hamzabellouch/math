import OAI.Analysis.FiniteFactor.Sampling.OrientedMoments

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceSamplingCutoff_le_half (s : ℕ) : sourceSamplingCutoff s ≤ 1/2 := by
  have hm : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
  have hp := sourceBlockSize_pos s
  calc
    sourceSamplingCutoff s ≤ (sourceBlockSize s : ℝ)^(-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = 1/(sourceBlockSize s : ℝ) := by rw [Real.rpow_neg_one,one_div]
    _ ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by linarith)

theorem sourceSampling_log_self_bound (s : ℕ) :
    (2/sourceSamplingWidth s)*Real.log (1/(2*sourceSamplingCutoff s)) ≤
      4*(sourceBlockSize s : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize s : ℝ) := by
  have hp := sourceSampling_parameters s
  have hm := sourceBlockSize_pos s
  have hl : Real.log (1/(2*sourceSamplingCutoff s)) ≤ Real.log (1/sourceSamplingCutoff s) :=
    Real.log_le_log (one_div_pos.mpr (mul_pos (by norm_num) hp.2.2)) (one_div_le_one_div_of_le hp.2.2 (by linarith [hp.2.2]))
  have he : Real.log (1/sourceSamplingCutoff s) = 2*Real.log (sourceBlockSize s : ℝ) := by
    unfold sourceSamplingCutoff
    rw [one_div,Real.log_inv,Real.log_rpow hm]
    ring
  have hw : (sourceSamplingWidth s)⁻¹ = (sourceBlockSize s : ℝ)^(3/5 : ℝ) := by
    unfold sourceSamplingWidth
    rw [show (-3/5 : ℝ) = -(3/5) by ring,Real.rpow_neg hm.le,inv_inv]
  calc
    _ ≤ (2/sourceSamplingWidth s)*(2*Real.log (sourceBlockSize s : ℝ)) :=
      mul_le_mul_of_nonneg_left (hl.trans_eq he) (div_nonneg (by norm_num) hp.1.le)
    _ = _ := by rw [div_eq_mul_inv,hw]; ring

/-- All tested source weights have the logarithmic self-pair bound in both
orientations. The harmless extra 1 includes triangular coordinates. -/
theorem sourceSampling_oriented_self_moment (stage : ℕ) (r b : Bool) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, ∫ t, samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s t ^ 2
      ∂unitIntervalMeasure ∂unitIntervalMeasure) ≤
      1+4*(sourceBlockSize stage : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize stage : ℝ) := by
  have hp := sourceSampling_parameters stage
  have hc := sourceSamplingCutoff_le_half stage
  have hlog : 0 ≤ Real.log (sourceBlockSize stage : ℝ) := Real.log_nonneg (by
    have hm : (100 : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (sourceStage stage).m_ge_100
    linarith)
  have herr : (0 : ℝ) ≤ 4*(sourceBlockSize stage : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize stage : ℝ) := by positivity
  cases b
  · have hb : (∫ s, ∫ t, samplingOrientedWeight r false (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s t ^ 2
        ∂unitIntervalMeasure ∂unitIntervalMeasure) ≤
        (2/sourceSamplingWidth stage)*Real.log (1/(2*sourceSamplingCutoff stage)) := by
      cases r
      · exact samplingTestedFirstWeight_square_integral _ _ E G hp.1 hp.2.1 hp.2.2 hc hE hG
      · exact samplingTestedSecondWeight_square_integral _ _ E G hp.1 hp.2.1 hp.2.2 hc hE hG
    exact (hb.trans (sourceSampling_log_self_bound stage)).trans (by linarith)
  · have hm := samplingOrientedWeight_measurable r true (sourceSamplingWidth stage)
      (sourceSamplingCutoff stage) E G hE hG
    have hb := samplingOrientedWeight_triangular_bounds r (sourceSamplingWidth stage)
      (sourceSamplingCutoff stage) E G
    have hi := sampling_square_integrable (unitIntervalMeasure.prod unitIntervalMeasure) _ 1 hm
      (fun p => hb p.1 p.2)
    rw [← integral_prod _ hi]
    have hle : (∫ p : ℝ × ℝ, samplingOrientedWeight r true (sourceSamplingWidth stage)
        (sourceSamplingCutoff stage) E G p.1 p.2 ^ 2 ∂unitIntervalMeasure.prod unitIntervalMeasure) ≤ 1 := by
      simpa using integral_mono_ae hi (integrable_const (1 : ℝ))
        (Eventually.of_forall (fun p => by nlinarith [(hb p.1 p.2).1,(hb p.1 p.2).2]))
    exact hle.trans (by linarith)

end
end FiniteFactor

end OAI
