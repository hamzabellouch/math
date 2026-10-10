import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace OAI

/-! # Numerical lower bound for the recovered scalar -/

namespace KadisonKastler

/-- The cubic-root error estimate is expressed using only square roots,
as in the tracial Cauchy–Schwarz calculation. -/
theorem recovery_compression_error_le {n N η : ℝ}
    (hn : 0 ≤ n) (hN : 0 < N) (hη : 0 ≤ η) (hNη : N * η = 100)
    (hsize : 100000000 * n ≤ N) :
    2 * N * Real.sqrt n * η * Real.sqrt η ≤ 1 / 5 := by
  let E := 2 * N * Real.sqrt n * η * Real.sqrt η
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have heq : E ^ 2 * N = 4000000 * n := by
    dsimp [E]
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hn, Real.sq_sqrt hη]
    calc
      _ = 4 * n * (N * η) ^ 3 := by ring
      _ = _ := by rw [hNη]; ring
  have hsq : E ^ 2 ≤ 1 / 25 := by
    nlinarith
  change E ≤ 1 / 5
  nlinarith

/-- The manuscript's choice `N ≥ 100 n (100π)^3` makes the recovered
scalar uniformly larger than one half. -/
theorem recovered_scalar_lower_bound {n N : ℕ} (hn : 1 ≤ n)
    (hsize : 100 * (n : ℝ) * (100 * Real.pi) ^ 3 ≤ N)
    {c : ℝ}
    (hc : 9 / 10 - 2 * Real.pi / (100 * Real.pi) -
      2 * N * Real.sqrt ((n : ℝ) - 1) * (100 / N) * Real.sqrt (100 / N) ≤ c) :
    1 / 2 ≤ c := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi1 : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi3 : 1 ≤ Real.pi ^ 3 := one_le_pow₀ hpi1
  have hsize' : 100000000 * (n : ℝ) ≤ N := by
    have he : 100 * (n : ℝ) * (100 * Real.pi) ^ 3 =
        100000000 * (n : ℝ) * Real.pi ^ 3 := by ring
    rw [he] at hsize
    have ht := mul_nonneg (show 0 ≤ 100000000 * (n : ℝ) by positivity)
      (sub_nonneg.mpr hpi3)
    nlinarith
  have hN : (0 : ℝ) < N := by nlinarith
  have he := recovery_compression_error_le (show 0 ≤ (n : ℝ) - 1 by linarith) hN
    (show 0 ≤ 100 / (N : ℝ) by positivity)
    (show (N : ℝ) * (100 / N) = 100 by field_simp)
    (show 100000000 * ((n : ℝ) - 1) ≤ N by linarith)
  have hratio : 2 * Real.pi / (100 * Real.pi) = (1 / 50 : ℝ) := by
    field_simp
    ring
  rw [hratio] at hc
  linarith

end KadisonKastler

end OAI
