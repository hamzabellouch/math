import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace OAI

/-! A rational Taylor approximation with an explicit magnitude and binary
precision parameter. This applies to the negative rational exponents in
the Gaussian heat kernel as well as to positive arguments. -/

open scoped BigOperators
namespace ContinuumCoulomb.RationalExponential

def order (M p : ℕ) : ℕ := 2 * (2 * M ^ 2 + p + 2)

def taylorSum (q : ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, q ^ j / (j.factorial : ℚ)

def approximate (M p : ℕ) (q : ℚ) : ℚ := taylorSum q (order M p)

private theorem factorial_bound (M p : ℕ) :
    2 ^ (p + 2) * M ^ order M p ≤ (order M p).factorial := by
  let N := 2 * M ^ 2 + p + 2
  have hprec : 2 ^ (p + 2) ≤ 2 ^ N :=
    Nat.pow_le_pow_right (by decide) (by dsimp [N]; omega)
  have hpow : 2 ^ N * M ^ (2 * N) ≤ N ^ N := by
    rw [pow_mul, ← mul_pow]
    apply Nat.pow_le_pow_left
    dsimp [N]
    omega
  have hfac : N ^ N ≤ (2 * N).factorial := by
    have h1 : N ^ N ≤ (N + 1) ^ N := Nat.pow_le_pow_left (Nat.le_succ N) N
    have h2 : (N + 1) ^ N ≤ N.factorial * (N + 1) ^ N := by
      simpa only [one_mul] using Nat.mul_le_mul_right ((N + 1) ^ N)
        (show 1 ≤ N.factorial from Nat.factorial_pos N)
    have h3 := @Nat.factorial_mul_pow_le_factorial N N
    rw [show N + N = 2 * N by omega] at h3
    exact h1.trans (h2.trans h3)
  exact (Nat.mul_le_mul_right (M ^ (2 * N)) hprec).trans (hpow.trans hfac)

theorem error (M p : ℕ) (q : ℚ) (hq : |(q : ℝ)| ≤ M) :
    |Real.exp (q : ℝ) - (approximate M p q : ℝ)| ≤ (2 ^ p : ℝ)⁻¹ := by
  let n := order M p
  have hpnonneg : 0 ≤ (p : ℝ) := by positivity
  have hx : ‖((q : ℝ) : ℂ)‖ / (n + 1 : ℕ) ≤ (1 / 2 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
    dsimp [n, order]
    push_cast
    nlinarith [sq_nonneg ((M : ℝ) - 1 / 4)]
  have hc := Complex.exp_bound' (x := ((q : ℝ) : ℂ)) (n := n) hx
  have hr : |Real.exp (q : ℝ) - (approximate M p q : ℝ)| ≤
      |(q : ℝ)| ^ n / (n.factorial : ℝ) * 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_exp,
      ← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
      ← Complex.ofReal_sum, ← Complex.ofReal_sub, approximate, taylorSum,
      Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, n] using hc
  have hpow : |(q : ℝ)| ^ n ≤ (M : ℝ) ^ n := pow_le_pow_left₀ (abs_nonneg _) hq n
  have hfac : (2 ^ (p + 2) : ℝ) * (M : ℝ) ^ n ≤ (n.factorial : ℝ) := by
    exact_mod_cast factorial_bound M p
  have hratio : (M : ℝ) ^ n / (n.factorial : ℝ) ≤ (2 ^ (p + 2) : ℝ)⁻¹ := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).mpr
    have hm : (M : ℝ) ^ n * 2 ^ (p + 2) ≤ (n.factorial : ℝ) := by
      simpa only [mul_comm] using hfac
    have hr' : (M : ℝ) ^ n ≤ (n.factorial : ℝ) / 2 ^ (p + 2) :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (p + 2))).mpr hm
    simpa only [div_eq_mul_inv, mul_comm] using hr'
  have hprec : (2 ^ (p + 2) : ℝ)⁻¹ * 2 ≤ (2 ^ p : ℝ)⁻¹ := by
    rw [pow_add]
    norm_num
    have hp : 0 ≤ (2 ^ p : ℝ)⁻¹ := by positivity
    nlinarith
  exact hr.trans ((mul_le_mul_of_nonneg_right
    ((div_le_div_of_nonneg_right hpow (by positivity)).trans hratio) (by norm_num)).trans hprec)

end ContinuumCoulomb.RationalExponential

end OAI
