import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace PoissonProfileSupport

theorem factorization {P : ℕ → ℝ} {k : ℝ}
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * P (n + 1) = k * P n) (n : ℕ) :
    P n = k ^ n / (Nat.factorial n : ℝ) * P 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      apply (mul_left_cancel₀ hn)
      rw [hrec, ih, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        pow_succ]
      field_simp

theorem normalized {P : ℕ → ℝ} {k : ℝ}
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * P (n + 1) = k * P n)
    (hprob : HasSum P 1) (n : ℕ) :
    P n = Real.exp (-k) * k ^ n / (Nat.factorial n : ℝ) := by
  have he : HasSum (fun i : ℕ => k ^ i / (Nat.factorial i : ℝ)) (Real.exp k) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp k
  have hp : HasSum P (Real.exp k * P 0) := by
    have hform : P = fun i => k ^ i / (Nat.factorial i : ℝ) * P 0 :=
      funext (factorization hrec)
    rw [hform]
    simpa using he.mul_right (P 0)
  have hzero : P 0 = Real.exp (-k) := by
    have h := hp.unique hprob
    have hexp : Real.exp k ≠ 0 := Real.exp_ne_zero k
    apply (mul_left_cancel₀ hexp)
    rw [h, ← Real.exp_add]
    simp
  rw [factorization hrec, hzero]
  ring

theorem bivariate_factorization {P : ℕ → ℕ → ℝ} {k : ℝ}
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (i j : ℕ) :
    P i j = k ^ i / (Nat.factorial i : ℝ) * P 0 j :=
  factorization (P := fun n => P n j) (k := k) (fun n => hrec n j) i

theorem column_hasSum {P : ℕ → ℕ → ℝ} {k : ℝ}
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (j : ℕ) :
    HasSum (fun i => P i j) (Real.exp k * P 0 j) := by
  have he : HasSum (fun i : ℕ => k ^ i / (Nat.factorial i : ℝ)) (Real.exp k) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp k
  have hform : (fun i => P i j) =
      fun i => k ^ i / (Nat.factorial i : ℝ) * P 0 j :=
    funext (fun i => bivariate_factorization hrec i j)
  rw [hform]
  exact he.mul_right (P 0 j)

theorem column_eq_zero {P : ℕ → ℕ → ℝ} {k : ℝ}
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    {j : ℕ} (hj : P 0 j = 0) (i : ℕ) : P i j = 0 := by
  rw [bivariate_factorization hrec i j, hj, mul_zero]

theorem weighted_sum_factorization {P : ℕ → ℕ → ℝ} {k : ℝ}
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ × ℕ => w p.2 * P p.1 p.2)) :
    (∑' p : ℕ × ℕ, w p.2 * P p.1 p.2) =
      Real.exp k * ∑' j : ℕ, w j * P 0 j := by
  calc
    (∑' p : ℕ × ℕ, w p.2 * P p.1 p.2) =
        ∑' i : ℕ, ∑' j : ℕ, w j * P i j := hs.tsum_prod
    _ = ∑' j : ℕ, ∑' i : ℕ, w j * P i j := hs.tsum_comm.symm
    _ = ∑' j : ℕ, w j * (Real.exp k * P 0 j) := by
      apply tsum_congr
      intro j
      rw [tsum_mul_left, (column_hasSum hrec j).tsum_eq]
    _ = ∑' j : ℕ, Real.exp k * (w j * P 0 j) := by
      apply tsum_congr
      intro j
      ring
    _ = Real.exp k * ∑' j : ℕ, w j * P 0 j := tsum_mul_left

theorem weighted_zero_row {P : ℕ → ℕ → ℝ} {k : ℝ}
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ × ℕ => w p.2 * P p.1 p.2)) :
    (∑' j : ℕ, w j * P 0 j) =
      Real.exp (-k) * ∑' p : ℕ × ℕ, w p.2 * P p.1 p.2 := by
  rw [weighted_sum_factorization hrec w hs, ← mul_assoc, ← Real.exp_add]
  simp

theorem first_moment_zero_row {P : ℕ → ℕ → ℝ} {k c : ℝ}
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (hmean : HasSum (fun p : ℕ × ℕ => (p.2 : ℝ) * P p.1 p.2) c) :
    (∑' j : ℕ, (j : ℝ) * P 0 j) = Real.exp (-k) * c := by
  rw [weighted_zero_row hrec (fun j => (j : ℝ)) hmean.summable, hmean.tsum_eq]

theorem zero_row_mass {P : ℕ → ℕ → ℝ} {k : ℝ}
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (hprob : HasSum (fun p : ℕ × ℕ => P p.1 p.2) 1) :
    (∑' j : ℕ, P 0 j) = Real.exp (-k) := by
  have hs : Summable (fun p : ℕ × ℕ => (1 : ℝ) * P p.1 p.2) := by
    simpa using hprob.summable
  have h := weighted_zero_row hrec (fun _ => 1) hs
  simpa only [one_mul, hprob.tsum_eq, mul_one] using h

theorem not_recurrence_of_uncovered {P : ℕ → ℕ → ℝ} {k : ℝ}
    (hcorner : P 0 0 = 0) (huncovered : 0 < ∑' i : ℕ, P i 0) :
    ¬ (∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j) := by
  intro hrec
  have hz : (∑' i : ℕ, P i 0) = 0 := by
    simp only [column_eq_zero hrec hcorner, tsum_zero]
  rw [hz] at huncovered
  exact lt_irrefl 0 huncovered

end PoissonProfileSupport
end Balanced

end OAI
