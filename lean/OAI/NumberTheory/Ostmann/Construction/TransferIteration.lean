import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-! # The reserved exponential lower bound through the transfers -/

namespace Ostmann

private theorem half_exponential_square (c q : ℝ) :
    Real.exp (-c) / 2 * Real.exp (-q) ^ 2 =
      Real.exp (-2 * q - c - Real.log 2) := by
  calc
    _ = (Real.exp (-c) * Real.exp (2 * -q)) / 2 := by
      rw [show Real.exp (2 * -q) = Real.exp (-q) ^ 2 by
        simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (-q) 2]
      ring
    _ = Real.exp (-c + 2 * -q) / 2 := by rw [Real.exp_add]
    _ = Real.exp ((-c + 2 * -q) - Real.log 2) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = _ := by congr 1; ring

theorem transfer_half_lower (x y D B t c : ℝ) (ht : 0 ≤ t)
    (hbudget : c + Real.log 2 ≤ t)
    (hx : Real.exp (-B * t) ≤ x)
    (hD : D ≤ Real.exp (-(2 * B + 3) * t))
    (htransfer : Real.exp (-c) * x ^ 2 ≤ D + y) :
    Real.exp (-c) / 2 * x ^ 2 ≤ y := by
  have hsmall : Real.exp (-(2 * B + 3) * t) ≤
      Real.exp (-c) / 2 * Real.exp (-B * t) ^ 2 := by
    calc
      _ ≤ Real.exp (-2 * (B * t) - c - Real.log 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by
        simpa only [neg_mul] using (half_exponential_square c (B * t)).symm
  have hxx : Real.exp (-B * t) ^ 2 ≤ x ^ 2 := by
    have hx0 := (Real.exp_pos (-B * t)).le
    nlinarith
  have hDx := hD.trans (hsmall.trans
    (mul_le_mul_of_nonneg_left hxx (by positivity)))
  nlinarith

/-- The reserve comes from the initial bound. The loss c + log 2 is
counted by the exact geometric multiplicity 2^j-1. -/
theorem transfer_iteration_lower (η : ℕ → ℂ) (D : ℕ → ℝ)
    (Bstar m c : ℝ) (hm : 0 ≤ m) (hbudget : c + Real.log 2 ≤ m)
    (hzero : Real.exp (-Bstar * m) ≤ ‖η 0‖)
    (hD : ∀ j, D j ≤ Real.exp (-(2 * (Bstar + 3) + 3) * (2 : ℝ) ^ j * m))
    (htransfer : ∀ j, Real.exp (-c) * ‖η j‖ ^ 2 ≤ D j + ‖η (j + 1)‖) :
    ∀ j, Real.exp (-((2 : ℝ) ^ j * Bstar * m +
      ((2 : ℝ) ^ j - 1) * (c + Real.log 2))) ≤ ‖η j‖ := by
  intro j
  induction j with
  | zero => simpa using hzero
  | succ j ih =>
    have hr : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have ht : 0 ≤ (2 : ℝ) ^ j * m := mul_nonneg (by positivity) hm
    have hc : c + Real.log 2 ≤ (2 : ℝ) ^ j * m := by nlinarith
    have hcoarse : Real.exp (-(Bstar + 3) * ((2 : ℝ) ^ j * m)) ≤ ‖η j‖ := by
      apply le_trans (Real.exp_le_exp.mpr ?_) ih
      have hloss := mul_le_mul_of_nonneg_left hbudget (sub_nonneg.mpr hr)
      nlinarith
    have hdiag : D j ≤ Real.exp (-(2 * (Bstar + 3) + 3) * ((2 : ℝ) ^ j * m)) := by
      simpa only [mul_assoc] using hD j
    have hhalf := transfer_half_lower ‖η j‖ ‖η (j + 1)‖ (D j)
      (Bstar + 3) ((2 : ℝ) ^ j * m) c ht hc hcoarse hdiag (htransfer j)
    have hsquare : Real.exp (-((2 : ℝ) ^ j * Bstar * m +
        ((2 : ℝ) ^ j - 1) * (c + Real.log 2))) ^ 2 ≤ ‖η j‖ ^ 2 := by
      have he := Real.exp_pos (-((2 : ℝ) ^ j * Bstar * m +
        ((2 : ℝ) ^ j - 1) * (c + Real.log 2)))
      nlinarith
    apply le_trans ?_ hhalf
    calc
      _ = Real.exp (-c) / 2 * Real.exp (-((2 : ℝ) ^ j * Bstar * m +
          ((2 : ℝ) ^ j - 1) * (c + Real.log 2))) ^ 2 := by
        rw [half_exponential_square, pow_succ]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsquare (by positivity)

end Ostmann

end OAI
