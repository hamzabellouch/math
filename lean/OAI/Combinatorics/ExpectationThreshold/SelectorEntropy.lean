import OAI.Combinatorics.ExpectationThreshold.SelectorEntropyDyadic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The selector's finite entropy estimate

After scaling row `i` by `4^(i+1)`, its binomial coefficient is bounded by
one term of the exponential series at `T * 2^(-(i+1))`. The sum of these
arguments is at most `T`, so their product is at most `exp T ≤ 3^T`.
This proves the row-count estimate directly, including rows of count zero.
-/

namespace TalagrandThreshold

open scoped BigOperators

/-- A finite series and its explicit remainder already give the needed slack. -/
private theorem selector_exp_one_le_three : Real.exp 1 ≤ 3 := by
  have h := Real.exp_bound' (x := (1 : ℝ)) (n := 3)
    (by norm_num) (by norm_num) (by norm_num)
  exact h.trans (by norm_num [Finset.sum_range_succ])

/-- A scaled binomial coefficient is bounded by an exponential-series term. -/
theorem selector_choose_le_scaled_exp (m t : ℕ) (d y : ℝ)
    (hd : 0 ≤ d) (hy : 0 ≤ y) (hm : (m : ℝ) ≤ d * y) :
    (m.choose t : ℝ) ≤ d ^ t * Real.exp y := by
  calc
    (m.choose t : ℝ) ≤ (m : ℝ) ^ t / (t.factorial : ℝ) :=
      Nat.choose_le_pow_div t m
    _ ≤ (d * y) ^ t / (t.factorial : ℝ) :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg m) hm t) (Nat.cast_nonneg _)
    _ = d ^ t * (y ^ t / (t.factorial : ℝ)) := by rw [mul_pow]; ring
    _ ≤ d ^ t * Real.exp y :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp y hy t)
        (pow_nonneg hd t)

/-- The actual finite entropy bound for the selector's row sizes and counts.
The statement also permits total count zero. -/
theorem selector_entropy_bound (s : ℕ) (m t : Fin s → ℕ)
    (hm : ∀ i, m i ≤ 2 ^ (i.val + 1) * (∑ j, t j)) :
    (∏ i, ((m i).choose (t i) : ℝ)) ≤
      ∏ i, (3 * 4 ^ (i.val + 1) : ℝ) ^ (t i) := by
  let T : ℕ := ∑ i, t i
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hrow (i : Fin s) :
      ((m i).choose (t i) : ℝ) ≤
        ((4 : ℝ) ^ (i.val + 1)) ^ (t i) *
          Real.exp ((T : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1)) := by
    have hbound : (m i : ℝ) ≤ (2 : ℝ) ^ (i.val + 1) * (T : ℝ) := by
      have hnat : m i ≤ 2 ^ (i.val + 1) * T := hm i
      exact_mod_cast hnat
    have hscale : (4 : ℝ) ^ (i.val + 1) *
        ((T : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1)) =
        (2 : ℝ) ^ (i.val + 1) * (T : ℝ) := by
      calc
        (4 : ℝ) ^ (i.val + 1) *
            ((T : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1)) =
            ((4 : ℝ) * (1 / 2 : ℝ)) ^ (i.val + 1) * (T : ℝ) := by
          rw [mul_pow]
          ring
        _ = (2 : ℝ) ^ (i.val + 1) * (T : ℝ) := by norm_num
    apply selector_choose_le_scaled_exp
      (m i) (t i) ((4 : ℝ) ^ (i.val + 1))
      ((T : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1))
    · exact pow_nonneg (by norm_num) _
    · exact mul_nonneg hT (pow_nonneg (by norm_num) _)
    · rw [hscale]
      exact hbound
  have hsum : (∑ i : Fin s, (T : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1)) ≤
      (T : ℝ) := by
    rw [← Finset.mul_sum]
    exact mul_le_of_le_one_right hT (selector_dyadic_sum_le_one s)
  have hexp : Real.exp (T : ℝ) ≤ (3 : ℝ) ^ T := by
    calc
      Real.exp (T : ℝ) = Real.exp 1 ^ T := by
        simpa only [mul_one] using Real.exp_nat_mul 1 T
      _ ≤ (3 : ℝ) ^ T :=
        pow_le_pow_left₀ (Real.exp_pos 1).le selector_exp_one_le_three T
  have hprod : (0 : ℝ) ≤ ∏ i : Fin s, ((4 : ℝ) ^ (i.val + 1)) ^ (t i) :=
    Finset.prod_nonneg (fun i _ => pow_nonneg (pow_nonneg (by norm_num) _) _)
  have hfactor : (∏ i, (3 * 4 ^ (i.val + 1) : ℝ) ^ (t i)) =
      (∏ i, ((4 : ℝ) ^ (i.val + 1)) ^ (t i)) * (3 : ℝ) ^ T := by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    exact mul_comm _ _
  calc
    (∏ i, ((m i).choose (t i) : ℝ)) ≤
        ∏ i, (((4 : ℝ) ^ (i.val + 1)) ^ (t i) *
          Real.exp ((T : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1))) :=
      Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hrow i)
    _ = (∏ i, ((4 : ℝ) ^ (i.val + 1)) ^ (t i)) *
        Real.exp (∑ i : Fin s, (T : ℝ) * (1 / 2 : ℝ) ^ (i.val + 1)) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    _ ≤ (∏ i, ((4 : ℝ) ^ (i.val + 1)) ^ (t i)) * Real.exp (T : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le hsum) hprod
    _ ≤ (∏ i, ((4 : ℝ) ^ (i.val + 1)) ^ (t i)) * (3 : ℝ) ^ T :=
      mul_le_mul_of_nonneg_left hexp hprod
    _ = ∏ i, (3 * 4 ^ (i.val + 1) : ℝ) ^ (t i) := hfactor.symm

end TalagrandThreshold

end OAI
