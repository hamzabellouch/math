import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandParameters
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMixedRealBins

namespace OAI

/-! Uniform scalar growth estimates for the actual MRT band endpoints.
These estimates bound the mixed-moment factorial cost for every band. -/

namespace TwoPointCorrelations

lemma mrt_log_log_band_upper (Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hQ : 1 ≤ Real.log Q) :
    Real.log (Real.log (mrtBandUpper Q j)) + 1 ≤
      8 * (j : ℝ) ^ 2 * (Real.log (Real.log Q) + 1) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hq0 : 0 < Real.log Q := by linarith
  have hl0 : 0 ≤ Real.log (Real.log Q) := Real.log_nonneg hQ
  have hlj : Real.log (j : ℝ) ≤ j :=
    (Real.log_le_sub_one_of_pos hj0).trans (by linarith)
  have hj2 : (j : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hlj
    (show 0 ≤ 4 * (j : ℝ) + 2 by positivity)
  have hq := mul_le_mul_of_nonneg_right hj2 hl0
  simp only [mrtBandUpper, Real.log_exp]
  rw [Real.log_mul (pow_ne_zero _ hj0.ne') (pow_ne_zero _ hq0.ne'),
    Real.log_pow, Real.log_pow]
  push_cast
  nlinarith

lemma mrt_log_band_lower_fourth (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) :
    (j : ℝ) ^ 4 * Real.log P ≤ Real.log (mrtBandLower P Q j) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp : (j : ℝ) ^ 4 ≤ (j : ℝ) ^ (4 * j) :=
    pow_le_pow_right₀ hj1 (by omega)
  have hq : 1 ≤ Real.log Q ^ (j - 1) := one_le_pow₀ hQ
  simp only [mrtBandLower, Real.log_exp]
  apply mul_le_mul_of_nonneg_right _ hP
  exact hp.trans (le_mul_of_one_le_right (by positivity) hq)

lemma mrt_band_adjacent_log_product (P Q : ℝ) (j : ℕ)
    (hP : 0 ≤ Real.log P) (hQ : 0 ≤ Real.log Q) :
    ((j : ℝ) + 1) ^ 2 * Real.log (mrtBandUpper Q j) * Real.log P ≤
      Real.log (mrtBandLower P Q (j + 1)) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hp : (j : ℝ) ^ (4 * j + 2) ≤ ((j : ℝ) + 1) ^ (4 * j + 2) :=
    pow_le_pow_left₀ hj0 (by linarith) _
  have he : ((j : ℝ) + 1) ^ 2 * (j : ℝ) ^ (4 * j + 2) ≤
      ((j : ℝ) + 1) ^ (4 * (j + 1)) := by
    calc
      _ ≤ ((j : ℝ) + 1) ^ 2 * ((j : ℝ) + 1) ^ (4 * j + 2) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right he (pow_nonneg hQ j)) hP
  simpa only [mrtBandUpper, mrtBandLower, Real.log_exp,
    Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_assoc] using hh

theorem mrt_band_factorial_separation {η P Q : ℝ} (hη : 0 ≤ η)
    (j : ℕ) (hj : 1 ≤ j) (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 4096 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P) :
    32 * ((j : ℝ) + 1) ^ 2 *
        (Real.log (Real.log (mrtBandUpper Q (j + 1))) + 1) ≤
      η * Real.log (mrtBandLower P Q j) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hl : 0 ≤ Real.log (Real.log Q) + 1 := by
    linarith [Real.log_nonneg hQ]
  have hu := mrt_log_log_band_upper Q (j + 1) (by omega) hQ
  simp only [Nat.cast_add, Nat.cast_one] at hu
  have hp : ((j : ℝ) + 1) ^ 4 ≤ 16 * (j : ℝ) ^ 4 := by
    calc
      _ ≤ (2 * (j : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by ring
  calc
    _ ≤ 32 * ((j : ℝ) + 1) ^ 2 *
        (8 * ((j : ℝ) + 1) ^ 2 * (Real.log (Real.log Q) + 1)) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = 256 * ((j : ℝ) + 1) ^ 4 * (Real.log (Real.log Q) + 1) := by ring
    _ ≤ 4096 * (j : ℝ) ^ 4 * (Real.log (Real.log Q) + 1) := by
      nlinarith [mul_le_mul_of_nonneg_right hp hl]
    _ = (j : ℝ) ^ 4 * (4096 * (Real.log (Real.log Q) + 1)) := by ring
    _ ≤ (j : ℝ) ^ 4 * (η * Real.log P) :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = η * ((j : ℝ) ^ 4 * Real.log P) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mrt_log_band_lower_fourth P Q j hj hP hQ) hη

theorem mrt_band_support_separation {η P Q : ℝ} (hη : 0 ≤ η)
    (j : ℕ) (hj : 1 ≤ j) (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 16 ≤ η * Real.log P) :
    8 * ((j : ℝ) + 1) ^ 2 * (Real.log (mrtBandUpper Q j) + Real.log 2) ≤
      η * Real.log (mrtBandLower P Q (j + 1)) := by
  have hy : 1 ≤ Real.log (mrtBandUpper Q j) := by
    have hh := mrt_band_index_le_log_upper Q j hj hQ
    exact (show (1 : ℝ) ≤ j by exact_mod_cast hj).trans hh
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hp := mul_le_mul_of_nonneg_left hbudget
    (show 0 ≤ ((j : ℝ) + 1) ^ 2 * Real.log (mrtBandUpper Q j) by positivity)
  calc
    _ ≤ 16 * ((j : ℝ) + 1) ^ 2 * Real.log (mrtBandUpper Q j) := by
      nlinarith [mul_le_mul_of_nonneg_left (show Real.log 2 ≤
        Real.log (mrtBandUpper Q j) by linarith)
        (show 0 ≤ 8 * ((j : ℝ) + 1) ^ 2 by positivity)]
    _ ≤ η * (((j : ℝ) + 1) ^ 2 * Real.log (mrtBandUpper Q j) * Real.log P) := by
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mrt_band_adjacent_log_product P Q j hP (by linarith)) hη

end TwoPointCorrelations

end OAI
