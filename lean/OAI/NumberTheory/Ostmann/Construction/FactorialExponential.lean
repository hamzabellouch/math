import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith

namespace OAI

/-! # Elementary exponential factorial bounds used in arrangement ratios -/

namespace Ostmann

theorem factorial_exp_lower {n : ℕ} (hn : 1 ≤ n) :
    Real.exp ((n : ℝ) * Real.log n - n) ≤ (n.factorial : ℝ) := by
  have h := Stirling.le_log_factorial_stirling (show n ≠ 0 by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hpi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.two_le_pi])
  calc
    _ ≤ Real.exp (Real.log (n.factorial : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := Real.exp_log (by exact_mod_cast Nat.factorial_pos n)

theorem factorial_exp_upper {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) * Real.log n) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  rw [Real.exp_nat_mul, Real.exp_log hn0]
  exact_mod_cast Nat.factorial_le_pow n

/-- Normalization of r independent blocks against all permutations of rm
slots produces the entropy gain -rm log r. -/
theorem block_factorial_ratio {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    (m.factorial : ℝ) ^ r / ((r * m).factorial : ℝ) ≤
      Real.exp ((r : ℝ) * m * (1 - Real.log r)) := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hr
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hu : (m.factorial : ℝ) ^ r ≤ Real.exp ((r : ℝ) * m * Real.log m) := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ m.factorial by positivity)
      (factorial_exp_upper hm) r
    rw [← Real.exp_nat_mul] at h
    convert h using 1
    congr 1
    ring
  have hl := factorial_exp_lower (Nat.mul_pos (by omega : 0 < r) (by omega : 0 < m))
  simp only [Nat.cast_mul, Real.log_mul (ne_of_gt hr0) (ne_of_gt hm0)] at hl
  apply (div_le_iff₀ (show (0 : ℝ) < (r * m).factorial by positivity)).mpr
  calc
    _ ≤ Real.exp ((r : ℝ) * m * Real.log m) := hu
    _ = Real.exp ((r : ℝ) * m * (1 - Real.log r)) *
        Real.exp ((r : ℝ) * m * (Real.log r + Real.log m) - (r : ℝ) * m) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (Real.exp_nonneg _)

end Ostmann

end OAI
