import OAI.Algebra.DepthFive.CeilArithmetic

namespace OAI

noncomputable section
namespace Problem335

/-- The elementary gate-count estimate, before specializing the block parameters. -/
theorem gateCount_le_pow (n t r : ℕ) (hn : 3 ≤ n)
    (ht : 2 ≤ t) (hr : r ≤ t) (htn : t ≤ n) :
    2 * n ^ 3 + r * n ^ 2 + r * n ^ (t + 1) + n ^ (r - 1) + 1 ≤
      n ^ (t + 3) := by
  have hn0 : 0 < n := by omega
  have hrn : r ≤ n := hr.trans htn
  have hfirst : 2 * n ^ 3 + r * n ^ 2 ≤ 3 * n ^ 3 := by
    have h := Nat.mul_le_mul_right (n ^ 2) hrn
    nlinarith [pow_succ n 2]
  have hsecond : r * n ^ (t + 1) ≤ n ^ (t + 2) := by
    calc
      r * n ^ (t + 1) ≤ n * n ^ (t + 1) :=
        Nat.mul_le_mul_right _ hrn
      _ = n ^ (t + 2) := by simp [pow_add]; ring
  have hthird : n ^ (r - 1) ≤ n ^ (t - 1) :=
    Nat.pow_le_pow_right hn0 (Nat.sub_le_sub_right hr 1)
  have hsmall : 3 * n ^ 3 ≤ n ^ (t + 2) := by
    calc
      3 * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hn
      _ = n ^ 4 := by ring
      _ ≤ n ^ (t + 2) := Nat.pow_le_pow_right hn0 (by omega)
  have htail : n ^ (t - 1) + 1 ≤ n ^ (t + 2) := by
    have h := Nat.pow_lt_pow_right (by omega : 1 < n) (show t - 1 < t + 2 by omega)
    omega
  have htotal :
      2 * n ^ 3 + r * n ^ 2 + r * n ^ (t + 1) + n ^ (r - 1) + 1 ≤
        3 * n ^ (t + 2) := by omega
  calc
    _ ≤ 3 * n ^ (t + 2) := htotal
    _ ≤ n * n ^ (t + 2) := Nat.mul_le_mul_right _ hn
    _ = n ^ (t + 3) := by simp [pow_add]; ring

/-- Conversion of the integer block gate count into the advertised real-power bound. -/
theorem gateCount_le_rpow (n t r : ℕ) (hn : 3 ≤ n)
    (ht : 2 ≤ t) (hr : r ≤ t) (htn : t ≤ n)
    (htsqrt : (t : ℝ) ≤ Real.sqrt (n : ℝ) + 1) :
    ((2 * n ^ 3 + r * n ^ 2 + r * n ^ (t + 1) + n ^ (r - 1) + 1 : ℕ) : ℝ) ≤
      (n : ℝ) ^ (Real.sqrt (n : ℝ) + 4) := by
  calc
    _ ≤ ((n ^ (t + 3) : ℕ) : ℝ) := by
      exact_mod_cast gateCount_le_pow n t r hn ht hr htn
    _ = (n : ℝ) ^ ((t + 3 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_cast
    _ ≤ (n : ℝ) ^ (Real.sqrt (n : ℝ) + 4) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (show 1 ≤ n by omega)
      · push_cast
        linarith

/-- The exceptional smallest size in the upper-bound estimate. -/
theorem upperGateBound_two_le_rpow :
    (upperGateBound 2 : ℝ) ≤ (2 : ℝ) ^ (Real.sqrt 2 + 4) := by
  have hcount : upperGateBound 2 = 30 := by
    norm_num [upperGateBound, ceilSqrt, ceilDiv, Nat.sqrt_two]
  rw [hcount]
  calc
    (30 : ℝ) ≤ (2 : ℝ) ^ (5 : ℕ) := by norm_num
    _ = (2 : ℝ) ^ (5 : ℝ) := (Real.rpow_natCast 2 5).symm
    _ ≤ (2 : ℝ) ^ (Real.sqrt 2 + 4) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
      linarith

/-- The explicit gate bound is at most `n^(sqrt n + 4)`. -/
theorem upperGateBound_le_rpow (n : ℕ) (hn : 2 ≤ n) :
    (upperGateBound n : ℝ) ≤ (n : ℝ) ^ (Real.sqrt (n : ℝ) + 4) := by
  rcases eq_or_lt_of_le hn with rfl | hn
  · exact upperGateBound_two_le_rpow
  · exact gateCount_le_rpow n (ceilSqrt n) (ceilDiv n (ceilSqrt n))
      (by omega) (two_le_ceilSqrt (by omega)) (ceilDiv_ceilSqrt_le n)
      (ceilSqrt_le_self n) (ceilSqrt_cast_le_real_sqrt_add_one n)

end Problem335

end

end OAI
