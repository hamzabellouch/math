import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

namespace OAI

/-!
# Rational Taylor construction of the large charge scale

Only `4D²+4` rational Taylor terms are used. The absolute exponential error
is at most one half, so rounding this explicit rational number gives the
constant-factor amplification required by the construction. No real-number
floor operation or unknown spectral quantity occurs in the algorithm.
-/

open scoped BigOperators
namespace ContinuumCoulomb

def amplificationOrder (D : ℕ) : ℕ := 2 * (2 * D ^ 2 + 2)

def amplificationTaylor (D : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (amplificationOrder D), (D : ℚ) ^ k / (k.factorial : ℚ)

def taylorAmplification (D : ℕ) : ℕ := Nat.ceil (amplificationTaylor D)

private theorem amplification_factorial_bound (D : ℕ) :
    4 * D ^ amplificationOrder D ≤ (amplificationOrder D).factorial := by
  let N := 2 * D ^ 2 + 2
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hfour : 4 ≤ 2 ^ N := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have hpow : 2 ^ N * D ^ (2 * N) ≤ N ^ N := by
    rw [pow_mul, ← mul_pow]
    apply Nat.pow_le_pow_left
    dsimp [N]
    omega
  have hfac : N ^ N ≤ (2 * N).factorial := by
    have h1 : N ^ N ≤ (N + 1) ^ N := Nat.pow_le_pow_left (Nat.le_succ N) N
    have h2 := Nat.mul_le_mul_right ((N + 1) ^ N)
      (show 1 ≤ N.factorial from Nat.factorial_pos N)
    have h3 := @Nat.factorial_mul_pow_le_factorial N N
    have heq : N + N = 2 * N := by omega
    rw [heq] at h3
    have h2' : (N + 1) ^ N ≤ N.factorial * (N + 1) ^ N := by
      simpa only [one_mul] using h2
    exact h1.trans (h2'.trans h3)
  exact (Nat.mul_le_mul_right (D ^ (2 * N)) hfour).trans (hpow.trans hfac)

theorem amplificationTaylor_error (D : ℕ) :
    |Real.exp (D : ℝ) - (amplificationTaylor D : ℝ)| ≤ 1 / 2 := by
  let n := amplificationOrder D
  have hn : 0 < n := by dsimp [n, amplificationOrder]; omega
  have hx : ‖(D : ℂ)‖ / (n + 1 : ℕ) ≤ (1 / 2 : ℝ) := by
    simp only [Complex.norm_natCast]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
    dsimp [n, amplificationOrder]
    push_cast
    nlinarith [sq_nonneg ((D : ℝ) - 1 / 4)]
  have hc := Complex.exp_bound' (x := (D : ℂ)) (n := n) hx
  have hr : |Real.exp (D : ℝ) - (amplificationTaylor D : ℝ)| ≤
      (D : ℝ) ^ n / (n.factorial : ℝ) * 2 := by
    simpa only [Complex.norm_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_exp,
      ← Complex.ofReal_pow, ← Complex.ofReal_div, ← Complex.ofReal_sum,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (D : ℝ) from Nat.cast_nonneg D),
      amplificationTaylor, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, n] using hc
  have hfac : 4 * (D : ℝ) ^ n ≤ (n.factorial : ℝ) := by
    exact_mod_cast amplification_factorial_bound D
  have hratio : (D : ℝ) ^ n / (n.factorial : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).mpr
    linarith
  exact hr.trans (by linarith)

theorem amplificationTaylor_ge_scale (D : ℕ) : (D : ℚ) + 1 ≤ amplificationTaylor D := by
  have hn : 2 ≤ amplificationOrder D := by unfold amplificationOrder; omega
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
    (f := fun k => (D : ℚ) ^ k / (k.factorial : ℚ))
    (by intro k _ _; positivity)
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, zero_add, pow_one, Nat.factorial_one, add_comm,
    amplificationTaylor] using h

theorem taylorAmplification_ge_scale (D : ℕ) : D + 1 ≤ taylorAmplification D := by
  have h : (D : ℚ) + 1 ≤ (taylorAmplification D : ℚ) :=
    (amplificationTaylor_ge_scale D).trans (Nat.le_ceil _)
  exact_mod_cast h

theorem taylorAmplification_pos (D : ℕ) : 0 < taylorAmplification D := by
  have h := taylorAmplification_ge_scale D
  omega

theorem taylorAmplification_bounds (D : ℕ) :
    Real.exp (D : ℝ) / 2 ≤ (taylorAmplification D : ℝ) ∧
      (taylorAmplification D : ℝ) ≤ 2 * Real.exp (D : ℝ) := by
  have herr := abs_le.mp (amplificationTaylor_error D)
  have hApos : (0 : ℚ) < amplificationTaylor D := by
    have h := amplificationTaylor_ge_scale D
    exact (by positivity : (0 : ℚ) < D + 1).trans_le h
  have hl : (amplificationTaylor D : ℝ) ≤ (taylorAmplification D : ℝ) := by
    exact_mod_cast (Nat.le_ceil (amplificationTaylor D))
  have hu : (taylorAmplification D : ℝ) ≤ (amplificationTaylor D : ℝ) + 1 := by
    exact_mod_cast (Nat.ceil_lt_add_one hApos.le).le
  have hexp : 1 ≤ Real.exp (D : ℝ) := Real.one_le_exp (by positivity)
  constructor
  · linarith
  · by_cases hD : D = 0
    · subst D
      norm_num [taylorAmplification, amplificationTaylor, amplificationOrder]
    · have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hD
      have hexp2 : 2 ≤ Real.exp (D : ℝ) := by linarith [Real.add_one_le_exp (D : ℝ)]
      linarith

end ContinuumCoulomb

end OAI
