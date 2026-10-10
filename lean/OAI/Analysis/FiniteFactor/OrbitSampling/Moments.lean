import OAI.Analysis.FiniteFactor.Sampling.TestedSecondMoment
import OAI.Analysis.FiniteFactor.OrbitSampling.Weights

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceSamplingWidth_le_half (s : ℕ) : sourceSamplingWidth s ≤ 1/2 := by
  have hm : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
  have hm0 : 0 ≤ (sourceBlockSize s : ℝ) := by positivity
  have he : sourceSamplingWidth s ≤ (sourceBlockSize s : ℝ)^(-1/2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hs : 2 ≤ Real.sqrt (sourceBlockSize s : ℝ) := by
    nlinarith [Real.sq_sqrt hm0,Real.sqrt_nonneg (sourceBlockSize s : ℝ)]
  apply he.trans
  rw [show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg hm0,← Real.sqrt_eq_rpow]
  simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs)

/-- Exact stage parameters discharge all cutoff/width assumptions in the
source's tested second-diagonal one-coordinate moment bound. -/
theorem sourceSampling_tested_second_moment (s : ℕ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∀ᵐ x ∂unitIntervalMeasure,
      0 ≤ samplingTestedSecondDensity (sourceSamplingWidth s) (sourceSamplingCutoff s) E G x ∧
      samplingTestedSecondDensity (sourceSamplingWidth s) (sourceSamplingCutoff s) E G x ≤ 2) ∧
    (∫ x, samplingTestedSecondDensity (sourceSamplingWidth s) (sourceSamplingCutoff s) E G x^2
      ∂unitIntervalMeasure) ≤ 1+4*(sourceBlockSize s : ℝ)^(-6/5 : ℝ) := by
  have hp := sourceSampling_parameters s
  have hhalf := sourceSamplingWidth_le_half s
  have hden : 0 < 1-sourceSamplingWidth s := by linarith [hp.2.1]
  have hb := samplingTestedSecondDensity_square (sourceSamplingWidth s) (sourceSamplingCutoff s)
    E G hp.1 hp.2.1 hp.2.2 hE hG
  have hi : 1/(1-sourceSamplingWidth s) ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
  have herror : (sourceSamplingWidth s)^2/(1-sourceSamplingWidth s)^2 ≤ 4*(sourceSamplingWidth s)^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    have hsq : (1/4 : ℝ) ≤ (1-sourceSamplingWidth s)^2 := by nlinarith
    nlinarith [sq_nonneg (sourceSamplingWidth s),mul_nonneg (sq_nonneg (sourceSamplingWidth s))
      (show 0 ≤ (1-sourceSamplingWidth s)^2-1/4 by linarith)]
  have he : (sourceSamplingWidth s)^2 = (sourceBlockSize s : ℝ)^(-6/5 : ℝ) := by
    unfold sourceSamplingWidth
    rw [← Real.rpow_natCast,← Real.rpow_mul (sourceBlockSize_pos s).le]
    norm_num
  exact ⟨hb.1.mono (fun x hx => ⟨hx.1,hx.2.trans hi⟩),hb.2.trans (by rw [← he]; linarith)⟩

end
end FiniteFactor

end OAI
