import Mathlib

namespace OAI

noncomputable section

namespace Problem313

/-- A deliberately generous quadratic-exponential estimate. -/
lemma quadratic_mul_exp_neg_eighth_le (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-t / 8) ≤ 256 := by
  have hlin : t / 16 ≤ Real.exp (t / 16) := by
    have h := Real.add_one_le_exp (t / 16)
    linarith
  have hsquare : (t / 16) ^ 2 ≤ (Real.exp (t / 16)) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hlin 2
  have hexp : (Real.exp (t / 16)) ^ 2 = Real.exp (t / 8) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hsquare
  have hquad : t ^ 2 ≤ 256 * Real.exp (t / 8) := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hquad (le_of_lt (Real.exp_pos (-t / 8)))
  have hcancel : Real.exp (t / 8) * Real.exp (-t / 8) = 1 := by
    rw [← Real.exp_add]
    have hzero : t / 8 + -t / 8 = 0 := by ring
    rw [hzero, Real.exp_zero]
  nlinarith [hcancel]

/-- The exponentially small term in the block argument, with ample constant slack. -/
lemma block_exponential_remainder_le (t ell : ℝ) (ht : 0 ≤ t)
    (hell : t / 2 - Real.log 2 ≤ ell) :
    (4 * Real.exp (-ell / 4)) * t ^ 2 ≤ 2048 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have harg : -ell / 4 ≤ Real.log 2 - t / 8 := by linarith
  have hmono : Real.exp (-ell / 4) ≤ 2 * Real.exp (-t / 8) := by
    calc
      Real.exp (-ell / 4) ≤ Real.exp (Real.log 2 + (-t / 8)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = 2 * Real.exp (-t / 8) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hquad := quadratic_mul_exp_neg_eighth_le t ht
  have hmul := mul_le_mul_of_nonneg_right hmono (sq_nonneg t)
  nlinarith

/-- A form requiring only the logarithmic lower bound used for the spectral tail. -/
lemma block_exponential_remainder_le_of_third (t ell : ℝ) (ht : 0 ≤ t)
    (hell : t / 3 ≤ ell) :
    (4 * Real.exp (-ell / 4)) * t ^ 2 ≤ 2304 := by
  have hquad := quadratic_mul_exp_neg_eighth_le (2 * t / 3) (by positivity)
  have harg : -(2 * t / 3) / 8 = -t / 12 := by ring
  rw [harg] at hquad
  have hmono : Real.exp (-ell / 4) ≤ Real.exp (-t / 12) :=
    Real.exp_le_exp.mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hmono (sq_nonneg t)
  nlinarith

/-- The fractional-power form of the block remainder estimate. -/
lemma block_rpow_remainder_le (t m : ℝ) (ht : 0 ≤ t) (hm : 0 < m)
    (hm_log : t / 3 ≤ Real.log m) :
    (4 * m ^ (-1 / 4 : ℝ)) * t ^ 2 ≤ 2304 := by
  rw [Real.rpow_def_of_pos hm]
  have harg : Real.log m * (-1 / 4 : ℝ) = -Real.log m / 4 := by ring
  rw [harg]
  exact block_exponential_remainder_le_of_third t (Real.log m) ht hm_log

end Problem313

end

end OAI
