import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem large_prime_weight_card_bound {n : ℕ} {u H : ℝ}
    (hu : 1 < u) (hH : 0 ≤ H) (hweight : Real.exp H < u ^ n.primeFactors.card) :
    2 * ⌊H / (2 * Real.log u)⌋₊ ≤ n.primeFactors.card := by
  have hu0 : 0 < u := zero_lt_one.trans hu
  have hlog : 0 < Real.log u := Real.log_pos hu
  have hl := Real.log_lt_log (Real.exp_pos H) hweight
  rw [Real.log_exp, Real.log_pow] at hl
  have hf := Nat.floor_le (div_nonneg hH (by positivity : (0 : ℝ) ≤ 2 * Real.log u))
  have hfm := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log u)).mp hf
  have hc : (2 : ℝ) * (⌊H / (2 * Real.log u)⌋₊ : ℝ) ≤ (n.primeFactors.card : ℝ) := by
    apply (mul_le_mul_iff_right₀ hlog).mp
    nlinarith
  exact_mod_cast hc

theorem exp_div_pow_floor_le {v t A : ℝ} (hv : 1 ≤ v) :
    Real.exp A / v ^ ⌊t⌋₊ ≤ Real.exp (A - (t - 1) * Real.log v) := by
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hlog : 0 ≤ Real.log v := Real.log_nonneg hv
  have hf : t - 1 ≤ (⌊t⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one t]
  have hp : v ^ ⌊t⌋₊ = Real.exp ((⌊t⌋₊ : ℝ) * Real.log v) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hv0 _)]
  rw [hp, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right hf hlog
  linarith

end Ostmann.QuadraticCenter

end OAI
