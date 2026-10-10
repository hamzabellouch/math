import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# The fair-bit exponential moment bound

Finite Taylor approximations with proved remainder bounds suffice for the
parameter used in the fair-bit tail bound.
-/

namespace QuantitativeVanDerWaerden

/-- The exponential moment bound at the fair-bit tail parameter. -/
theorem cosh_half_le_exp_eighth : Real.cosh (1 / 2 : ℝ) ≤ Real.exp (1 / 8 : ℝ) := by
  have ah : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_nonneg (by norm_num)
  have ae : |(1 / 8 : ℝ)| = 1 / 8 := abs_of_nonneg (by norm_num)
  have hp := Real.exp_bound (x := (1 / 2 : ℝ)) (by rw [ah]; norm_num)
    (n := 4) (by norm_num)
  have hm := Real.exp_bound (x := -(1 / 2 : ℝ)) (by rw [abs_neg, ah]; norm_num)
    (n := 4) (by norm_num)
  have he := Real.exp_bound (x := (1 / 8 : ℝ)) (by rw [ae]; norm_num)
    (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg, ah, ae] at hp hm he
  rw [abs_le] at hp hm he
  rw [Real.cosh_eq]
  linarith [hp.2, hm.2, he.1]

end QuantitativeVanDerWaerden

end OAI
