import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace OAI

/-!
# Quantitative flat exponential

The usual flat exponential has Gevrey order two.  The proof keeps the
factorial-weighted coefficient sum of its derivative polynomials, so that
the estimate is uniform on the entire real line.
-/

open Polynomial Finset

noncomputable section
namespace RegularPointCoordinates

private def gluePolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X ^ 2 * (gluePolynomial n - (gluePolynomial n).derivative)

private def coefficientWeight (p : ℝ[X]) (N : ℕ) : ℝ :=
  ∑ k ∈ range N, |p.coeff k| * (k.factorial : ℝ)

private theorem gluePolynomial_degree (n : ℕ) :
    (gluePolynomial n).natDegree ≤ 2 * n := by
  induction n with
  | zero => simp [gluePolynomial]
  | succ n ih =>
    have hd := (natDegree_derivative_le (gluePolynomial n)).trans (Nat.sub_le _ _)
    have hs := natDegree_sub_le (gluePolynomial n) (gluePolynomial n).derivative
    have hm := natDegree_mul_le (p := (X : ℝ[X]) ^ 2)
      (q := gluePolynomial n - (gluePolynomial n).derivative)
    simp only [natDegree_X_pow] at hm
    change (X ^ 2 * (gluePolynomial n - (gluePolynomial n).derivative)).natDegree ≤ _
    omega

private theorem coefficientWeight_shift (p : ℝ[X]) (N : ℕ) :
    coefficientWeight (X ^ 2 * p) (N + 2) =
      ∑ k ∈ range N, |p.coeff k| * ((k + 2).factorial : ℝ) := by
  rw [coefficientWeight, show N + 2 = 2 + N by omega, sum_range_add]
  simp only [sum_range_succ, sum_range_zero, coeff_X_pow_mul',
    show ¬2 ≤ 0 by omega, show ¬2 ≤ 1 by omega, ite_false, abs_zero, zero_mul,
    zero_add, add_zero]
  apply sum_congr rfl
  intro k hk
  rw [ite_eq_left (by omega), show 2 + k - 2 = k by omega, Nat.add_comm 2 k]

private theorem coefficientWeight_step (p : ℝ[X]) (N : ℕ)
    (hp : p.natDegree < N) :
    coefficientWeight (X ^ 2 * (p - p.derivative)) (N + 2) ≤
      (2 * (N : ℝ) * (N + 1)) * coefficientWeight p N := by
  rw [coefficientWeight_shift]
  have hlast : p.coeff N = 0 := coeff_eq_zero_of_natDegree_lt hp
  have hshift : (∑ k ∈ range N, |p.coeff (k + 1)| * ((k + 1).factorial : ℝ)) ≤
      coefficientWeight p N := by
    have heq := sum_range_succ' (fun k => |p.coeff k| * (k.factorial : ℝ)) N
    rw [sum_range_succ, hlast, abs_zero, zero_mul, add_zero] at heq
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one] at heq
    change _ ≤ ∑ k ∈ range N, |p.coeff k| * (k.factorial : ℝ)
    linarith [abs_nonneg (p.coeff 0)]
  have hfirst : (∑ k ∈ range N, |p.coeff k| * ((k + 2).factorial : ℝ)) ≤
      ((N : ℝ) * (N + 1)) * coefficientWeight p N := by
    rw [coefficientWeight, mul_sum]
    apply sum_le_sum
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast mem_range.mp hk
    have hk'' : (k : ℝ) + 2 ≤ N + 1 := by linarith
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    nlinarith only [mul_le_mul hk' hk'' (by positivity : 0 ≤ (k : ℝ) + 2)
      (by positivity : 0 ≤ (N : ℝ)),
      mul_nonneg (abs_nonneg (p.coeff k)) (by positivity : 0 ≤ (k.factorial : ℝ))]
  have hsecond : (∑ k ∈ range N,
      |p.coeff (k + 1)| * (k + 1 : ℝ) * ((k + 2).factorial : ℝ)) ≤
      ((N : ℝ) * (N + 1)) * coefficientWeight p N := by
    calc
      _ ≤ ((N : ℝ) * (N + 1)) *
          ∑ k ∈ range N, |p.coeff (k + 1)| * ((k + 1).factorial : ℝ) := by
        rw [mul_sum]
        apply sum_le_sum
        intro k hk
        have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast mem_range.mp hk
        have hk'' : (k : ℝ) + 2 ≤ N + 1 := by linarith
        rw [Nat.factorial_succ (k + 1), Nat.cast_mul]
        push_cast
        nlinarith only [mul_le_mul hk' hk'' (by positivity : 0 ≤ (k : ℝ) + 2)
          (by positivity : 0 ≤ (N : ℝ)),
          mul_nonneg (abs_nonneg (p.coeff (k + 1)))
            (by positivity : 0 ≤ ((k + 1).factorial : ℝ))]
      _ ≤ _ := mul_le_mul_of_nonneg_left hshift (by positivity)
  calc
    _ ≤ ∑ k ∈ range N, (|p.coeff k| +
        |p.coeff (k + 1)| * (k + 1 : ℝ)) * ((k + 2).factorial : ℝ) := by
      apply sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [coeff_sub, coeff_derivative, abs_mul, Nat.cast_add, Nat.cast_one,
        abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) + 1)] using
        abs_sub (p.coeff k) (p.coeff (k + 1) * (k + 1 : ℝ))
    _ = (∑ k ∈ range N, |p.coeff k| * ((k + 2).factorial : ℝ)) +
        ∑ k ∈ range N,
          |p.coeff (k + 1)| * (k + 1 : ℝ) * ((k + 2).factorial : ℝ) := by
      simp_rw [add_mul, sum_add_distrib]
    _ ≤ _ := by linarith

private theorem gluePolynomial_weight (n : ℕ) :
    coefficientWeight (gluePolynomial n) (2 * n + 1) ≤
      8 ^ n * (n.factorial : ℝ) ^ 2 := by
  induction n with
  | zero => norm_num [coefficientWeight, gluePolynomial]
  | succ n ih =>
    have hstep := coefficientWeight_step (gluePolynomial n) (2 * n + 1)
      (by have := gluePolynomial_degree n; omega)
    change coefficientWeight (gluePolynomial (n + 1)) (2 * (n + 1) + 1) ≤ _
    rw [gluePolynomial, show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
    calc
      _ ≤ (2 * ((2 * n + 1 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) + 1)) *
          coefficientWeight (gluePolynomial n) (2 * n + 1) := hstep
      _ ≤ (8 * (n + 1 : ℝ) ^ 2) * (8 ^ n * (n.factorial : ℝ) ^ 2) := by
        apply mul_le_mul _ ih (by unfold coefficientWeight; positivity) (by positivity)
        push_cast
        nlinarith
      _ = _ := by rw [pow_succ, Nat.factorial_succ]; push_cast; ring

private theorem gluePolynomial_derivative (n : ℕ) :
    iteratedDeriv n expNegInvGlue =
      fun x => (gluePolynomial n).eval x⁻¹ * expNegInvGlue x := by
  induction n with
  | zero => simp [gluePolynomial]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (gluePolynomial n) x).deriv

/-- The standard flat exponential is globally Gevrey of order two. -/
theorem norm_iteratedDeriv_expNegInvGlue_le (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n expNegInvGlue x‖ ≤ 8 ^ n * (n.factorial : ℝ) ^ 2 := by
  rw [gluePolynomial_derivative, Real.norm_eq_abs]
  dsimp only
  by_cases hx : x ≤ 0
  · simp only [expNegInvGlue.zero_of_nonpos hx, mul_zero, abs_zero]
    positivity
  have hx' : 0 < x := lt_of_not_ge hx
  have hf : 0 ≤ expNegInvGlue x := expNegInvGlue.nonneg x
  have hexp (k : ℕ) : (x⁻¹) ^ k * expNegInvGlue x ≤ (k.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp x⁻¹ (inv_nonneg.mpr hx'.le) k
    rw [div_le_iff₀ (by positivity)] at h
    rw [expNegInvGlue, ite_eq_right hx, Real.exp_neg]
    apply (mul_le_mul_of_nonneg_right h (inv_nonneg.mpr (Real.exp_pos _).le)).trans_eq
    field_simp
  calc
    _ ≤ coefficientWeight (gluePolynomial n) (2 * n + 1) := by
      rw [(gluePolynomial n).eval_eq_sum_range' (n := 2 * n + 1)
        (by have := gluePolynomial_degree n; omega) x⁻¹, sum_mul, coefficientWeight]
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro k hk
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hx'.le) _),
        abs_of_nonneg hf, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hexp k) (abs_nonneg _)
    _ ≤ _ := gluePolynomial_weight n

end RegularPointCoordinates

end

end OAI
