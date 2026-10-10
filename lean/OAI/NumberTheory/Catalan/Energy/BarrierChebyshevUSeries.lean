import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem barrierChebyshevU_abs_le (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(Chebyshev.U ℝ (k : ℤ)).eval x| ≤ (k : ℝ) + 1 := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have h := Chebyshev.abs_iterate_derivative_T_real_le ((k : ℤ) + 1) 1 hx
  simp only [Function.iterate_one] at h
  rw [Chebyshev.derivative_T_eval_one, Chebyshev.T_derivative_eq_U] at h
  have hm : ((k : ℝ) + 1) * |(Chebyshev.U ℝ (k : ℤ)).eval x| ≤
      ((k : ℝ) + 1) * ((k : ℝ) + 1) := by
    simpa only [add_sub_cancel_right, eval_mul, eval_intCast, eval_add, eval_natCast, eval_one,
      Int.cast_add, Int.cast_natCast, Int.cast_one, abs_mul, abs_of_pos hk,
      pow_two] using h
  exact le_of_mul_le_mul_left hm hk

theorem barrierChebyshevU_summable {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ) * z ^ k) := by
  have hnorm : ‖(‖z‖ : ℝ)‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)] using hz
  have hmajor : Summable (fun k : ℕ => ((k : ℝ) + 1) * ‖z‖ ^ k) := by
    simpa only [add_mul, one_mul] using
      (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable.add
        (summable_geometric_of_norm_lt_one hnorm)
  refine hmajor.of_norm_bounded ?_
  intro k
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (barrierChebyshevU_abs_le k hx)
      (pow_nonneg (norm_nonneg z) k)

private theorem barrierChebyshevU_recurrence_complex (k : ℕ) (x : ℝ) :
    (((Chebyshev.U ℝ ((k + 2 : ℕ) : ℤ)).eval x : ℝ) : ℂ) =
      2 * (x : ℂ) * (((Chebyshev.U ℝ ((k + 1 : ℕ) : ℤ)).eval x : ℝ) : ℂ) -
        (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ) := by
  have h := congrArg (fun p : ℝ[X] => ((p.eval x : ℝ) : ℂ))
    (Chebyshev.U_add_two ℝ (k : ℤ))
  simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, eval_sub, eval_mul, eval_ofNat, eval_X,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat] using h

theorem barrierChebyshevU_hasSum {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ) * z ^ k)
      (1 / (1 - 2 * (x : ℂ) * z + z ^ 2)) := by
  let f : ℕ → ℂ := fun k => (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ) * z ^ k
  let S : ℂ := ∑' k, f k
  have hs : HasSum f S := (barrierChebyshevU_summable hx hz).hasSum
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : f 1 = 2 * (x : ℂ) * z := by simp [f, Chebyshev.U_one]
  have h1 : HasSum (fun k : ℕ => f (k + 1)) (S - 1) := by
    simpa only [Finset.sum_range_one, hf0] using (hasSum_nat_add_iff' 1).2 hs
  have h2 : HasSum (fun k : ℕ => f (k + 2)) (S - (1 + 2 * (x : ℂ) * z)) := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hf0, hf1] using
      (hasSum_nat_add_iff' 2).2 hs
  have hrec : ∀ k : ℕ, f (k + 2) =
      (2 * (x : ℂ) * z) * f (k + 1) - z ^ 2 * f k := by
    intro k
    dsimp only [f]
    rw [barrierChebyshevU_recurrence_complex k x]
    simp only [pow_add, pow_one]
    ring
  have hrecSum : HasSum (fun k : ℕ => f (k + 2))
      ((2 * (x : ℂ) * z) * (S - 1) - z ^ 2 * S) :=
    ((h1.mul_left (2 * (x : ℂ) * z)).sub (hs.mul_left (z ^ 2))).congr_fun hrec
  have heq := h2.unique hrecSum
  have hmul : (1 - 2 * (x : ℂ) * z + z ^ 2) * S = 1 := by
    linear_combination heq
  have hden : 1 - 2 * (x : ℂ) * z + z ^ 2 ≠ 0 := by
    intro hzero
    simp only [hzero, zero_mul, zero_ne_one] at hmul
  have hS : S = 1 / (1 - 2 * (x : ℂ) * z + z ^ 2) := by
    apply (eq_div_iff hden).2
    simpa only [mul_comm] using hmul
  rw [hS] at hs
  exact hs

end InternalCatalan

end

end OAI
