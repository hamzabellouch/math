import OAI.NumberTheory.TwoPointCorrelations.MRTMixedScale
import OAI.NumberTheory.TwoPointCorrelations.MRTRealPrimeBins

namespace OAI

/-! The actual real prime-bin threshold survives the integer endpoint
used by the finite mixed-moment theorem. -/

namespace TwoPointCorrelations

theorem mrt_mixed_real_bin_threshold {η Y u τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ) (hY : 1 < Y)
    (hu : 1 ≤ u) (hτ : 0 ≤ τ)
    (hcost : mrtAmplificationCost (mrtAmplificationOrder ⌈Y⌉₊ u)
        (Real.log (⌈Y⌉₊ : ℝ)) (mrtFrequencyExponent η j) ≤
      η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) *
        (τ + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
        ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
          (2 * mrtAmplificationOrder ⌈Y⌉₊ u) ≤
      (τ + 1) * Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hc := mrt_real_prime_bin_ceil hY
  have hlog : Real.log Y ≤ Real.log (⌈Y⌉₊ : ℝ) :=
    Real.log_le_log (by linarith) hc.2.1
  have ha := mrtFrequencyExponent_nonneg hη hη' j
  have hden : Real.exp (-mrtFrequencyExponent η j * Real.log (⌈Y⌉₊ : ℝ)) ≤
      Real.exp (-mrtFrequencyExponent η j * Real.log Y) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlog (by linarith))
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le hden
    (2 * mrtAmplificationOrder ⌈Y⌉₊ u)
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity) hp).trans
  exact mrt_mixed_threshold_amplification hη hη'
    (by exact_mod_cast hc.1) hu hτ j hcost

theorem mrt_mixed_real_bin_separation {η Y u τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ) (hY : 1 < Y)
    (hlogY : 1 ≤ Real.log Y)
    (hYu : Real.log (⌈Y⌉₊ : ℝ) ≤ Real.log u) (hu0 : 0 < u) (hτ : 0 ≤ τ)
    (hsep : 32 * ((j : ℝ) + 2) ^ 2 * (Real.log (Real.log u) + 1) ≤
      η * Real.log Y)
    (hsize : 8 * ((j : ℝ) + 2) ^ 2 * (Real.log Y + Real.log 2) ≤
      η * Real.log u) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) *
        (τ + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
        ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
          (2 * mrtAmplificationOrder ⌈Y⌉₊ u) ≤
      (τ + 1) * Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hc := mrt_real_prime_bin_ceil hY
  have hlog : Real.log Y ≤ Real.log (⌈Y⌉₊ : ℝ) :=
    Real.log_le_log (by linarith) hc.2.1
  apply mrt_mixed_real_bin_threshold hη hη' j hY
    ((Real.log_nonneg_iff hu0).mp (by linarith)) hτ
  apply mrt_amplification_cost_of_separation hη j
    (by exact_mod_cast (show 0 < ⌈Y⌉₊ by omega)) hu0 (hlogY.trans hlog) hYu
  · exact hsep.trans (mul_le_mul_of_nonneg_left hlog hη)
  · exact (mul_le_mul_of_nonneg_left hc.2.2.2 (by positivity)).trans hsize

end TwoPointCorrelations

end OAI
