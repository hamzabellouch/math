import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandLogGrowth

namespace OAI

/-! The numerical mixed-moment coefficient on two successive actual
MRT bands. The only initial scale condition is stated on P and Q. -/

namespace TwoPointCorrelations

theorem mrt_actual_band_mixed_bound {η P Q Y u τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hYlo : Real.exp (-1) * mrtBandLower P Q (j + 1) ≤ Y)
    (hYhi : Y ≤ mrtBandUpper Q (j + 1))
    (hulo : Real.exp (-1) * mrtBandLower P Q (j + 2) ≤ u)
    (huhi : u ≤ mrtBandUpper Q (j + 2)) (hτ : 0 ≤ τ) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) *
        (τ + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
        ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
          (2 * mrtAmplificationOrder ⌈Y⌉₊ u) ≤
      (τ + 1) * Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hP0 : 0 ≤ Real.log P := by linarith
  have hbase (k : ℕ) (hk : 1 ≤ k) :
      2 ≤ Real.log (mrtBandLower P Q k) := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hh := mrt_log_band_lower_fourth P Q k hk hP0 hQ
    have hp : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ hk1
    have hp2 : (2 : ℝ) ≤ (k : ℝ) ^ 4 * Real.log P := by
      have hmul := mul_le_mul hp hP (by norm_num : (0 : ℝ) ≤ 2) (by positivity)
      norm_num at hmul
      exact hmul
    exact hp2.trans hh
  have hY0 : 0 < Y := (mul_pos (Real.exp_pos _) (Real.exp_pos _)).trans_le hYlo
  have hu0 : 0 < u := (mul_pos (Real.exp_pos _) (Real.exp_pos _)).trans_le hulo
  have hlogYlo : Real.log (mrtBandLower P Q (j + 1)) - 1 ≤ Real.log Y := by
    have hh := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hYlo
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp] at hh
    change -1 + Real.log (mrtBandLower P Q (j + 1)) ≤ Real.log Y at hh
    linarith
  have hlogulo : Real.log (mrtBandLower P Q (j + 2)) - 1 ≤ Real.log u := by
    have hh := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hulo
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp] at hh
    change -1 + Real.log (mrtBandLower P Q (j + 2)) ≤ Real.log u at hh
    linarith
  have hybase := hbase (j + 1) (by omega)
  have hubase := hbase (j + 2) (by omega)
  have hlogY : 1 ≤ Real.log Y := by linarith
  have hlogu : 1 ≤ Real.log u := by linarith
  have hYhalf : Real.log (mrtBandLower P Q (j + 1)) / 2 ≤ Real.log Y := by linarith
  have huhalf : Real.log (mrtBandLower P Q (j + 2)) / 2 ≤ Real.log u := by linarith
  have hY1 : 1 < Y := (Real.log_pos_iff hY0.le).mp (by linarith)
  have hlogYhi : Real.log Y ≤ Real.log (mrtBandUpper Q (j + 1)) :=
    Real.log_le_log hY0 hYhi
  have hloguhi : Real.log u ≤ Real.log (mrtBandUpper Q (j + 2)) :=
    Real.log_le_log hu0 huhi
  have hhalfBudget : 4096 * (Real.log (Real.log Q) + 1) ≤ (η / 2) * Real.log P := by
    linarith
  have hsep0 := mrt_band_factorial_separation (show 0 ≤ η / 2 by positivity)
    (j + 1) (by omega) hP0 hQ hhalfBudget
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, show 1 + 1 = 2 by decide] at hsep0
  have hsep : 32 * ((j : ℝ) + 2) ^ 2 * (Real.log (Real.log u) + 1) ≤
      η * Real.log Y := by
    calc
      _ ≤ 32 * ((j : ℝ) + 2) ^ 2 *
          (Real.log (Real.log (mrtBandUpper Q (j + 2))) + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (Real.log_le_log (by linarith) hloguhi) le_rfl
      _ ≤ (η / 2) * Real.log (mrtBandLower P Q (j + 1)) := by
        convert hsep0 using 1
        ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hYhalf hη]
  have h16 : 16 ≤ (η / 2) * Real.log P := by
    have hl := Real.log_nonneg hQ
    linarith
  have hsize0 := mrt_band_support_separation (show 0 ≤ η / 2 by positivity)
    (j + 1) (by omega) hP0 hQ h16
  simp only [Nat.add_assoc, show (1 : ℕ) + 1 = 2 by decide,
    Nat.cast_add, Nat.cast_one] at hsize0
  have hsize : 8 * ((j : ℝ) + 2) ^ 2 * (Real.log Y + Real.log 2) ≤
      η * Real.log u := by
    calc
      _ ≤ 8 * ((j : ℝ) + 2) ^ 2 *
          (Real.log (mrtBandUpper Q (j + 1)) + Real.log 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hlogYhi le_rfl) (by positivity)
      _ ≤ (η / 2) * Real.log (mrtBandLower P Q (j + 2)) := by
        convert hsize0 using 1
        ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left huhalf hη]
  have hc := mrt_real_prime_bin_ceil hY1
  have hYu : Real.log (⌈Y⌉₊ : ℝ) ≤ Real.log u := by
    have hmult : 1 ≤ 8 * ((j : ℝ) + 2) ^ 2 := by
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith [sq_nonneg (j : ℝ)]
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hh := le_mul_of_one_le_left
      (show 0 ≤ Real.log Y + Real.log 2 by linarith) hmult
    have he : η * Real.log u ≤ Real.log u :=
      mul_le_of_le_one_left (by linarith) (by linarith)
    exact hc.2.2.2.trans (hh.trans (hsize.trans he))
  exact mrt_mixed_real_bin_separation hη hη' j hY1 hlogY hYu hu0 hτ hsep hsize

end TwoPointCorrelations

end OAI
