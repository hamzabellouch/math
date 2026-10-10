import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace OAI

/-! The finite-catalog error in the three deletion estimates is
negligible even when every bin uses a different interval. -/

namespace TwoPointCorrelations

open Filter

lemma deletion_comparison_error_bound (L C b d q S V : ℝ)
    (hL : 4800 ≤ L) (hC : 0 ≤ C) (hCL : C + 104 ≤ L)
    (hb0 : 0 ≤ b) (hd0 : 0 ≤ d) (hq0 : 0 ≤ q)
    (hb : b ≤ Real.exp (C * Real.log L)) (hd : d ≤ Real.exp (2 * L))
    (hq : q ≤ Real.exp (100 * L ^ 2)) (hS : 1 ≤ S) (hV : 1 ≤ V) :
    ((3 * b * d * q + b * Real.exp (101 * L)) * Real.exp (-(L ^ 9))) /
      (S * V) ≤ Real.exp (-L ^ (9 / 10 : ℝ)) := by
  have hL0 : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hcLog := mul_le_mul_of_nonneg_left hlog hC
  have hcL := mul_le_mul_of_nonneg_right hCL hL0
  have h101 := mul_le_mul_of_nonneg_right (show (101 : ℝ) ≤ L by linarith) (sq_nonneg L)
  have hp1 : C * Real.log L + 2 * L + 100 * L ^ 2 ≤ L ^ 3 := by nlinarith
  have hp2 : C * Real.log L + 101 * L ≤ L ^ 3 := by nlinarith
  have hprod : b * d * q ≤ Real.exp (L ^ 3) := by
    calc
      _ ≤ Real.exp (C * Real.log L) * Real.exp (2 * L) * Real.exp (100 * L ^ 2) :=
        mul_le_mul (mul_le_mul hb hd hd0 (Real.exp_pos _).le) hq hq0
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      _ = Real.exp (C * Real.log L + 2 * L + 100 * L ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr hp1
  have hother : b * Real.exp (101 * L) ≤ Real.exp (L ^ 3) := by
    calc
      _ ≤ Real.exp (C * Real.log L) * Real.exp (101 * L) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ = Real.exp (C * Real.log L + 101 * L) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hp2
  have h34 : L ^ 3 + 3 ≤ L ^ 4 := by
    have hh := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ L by linarith) (pow_nonneg hL0 3)
    have hp : 3 ≤ L ^ 3 := (show (3 : ℝ) ≤ L by linarith).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ hL1 (show 1 ≤ 3 by norm_num))
    nlinarith
  have hcoefficient : 3 * b * d * q + b * Real.exp (101 * L) ≤ Real.exp (L ^ 4) := by
    calc
      _ ≤ 4 * Real.exp (L ^ 3) := by nlinarith
      _ ≤ Real.exp 3 * Real.exp (L ^ 3) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (3 : ℝ)]) (Real.exp_pos _).le
      _ = Real.exp (L ^ 3 + 3) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr h34
  have hpower : L ^ 4 + L ≤ L ^ 9 := by
    have h45 : 2 * L ^ 4 ≤ L ^ 5 := by
      have hh := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ L by linarith) (pow_nonneg hL0 4)
      nlinarith
    have h59 : L ^ 5 ≤ L ^ 9 := pow_le_pow_right₀ hL1 (by norm_num)
    have h14 : L ≤ L ^ 4 := by
      have hh : L ^ 1 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
      simpa only [pow_one] using hh
    linarith
  have hsmall : L ^ (9 / 10 : ℝ) ≤ L := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL1
      (show (9 / 10 : ℝ) ≤ 1 by norm_num)
  have hSV : 1 ≤ S * V := by nlinarith
  have hnonneg : 0 ≤ (3 * b * d * q + b * Real.exp (101 * L)) * Real.exp (-(L ^ 9)) := by
    positivity
  calc
    _ ≤ (3 * b * d * q + b * Real.exp (101 * L)) * Real.exp (-(L ^ 9)) :=
      div_le_self hnonneg hSV
    _ ≤ Real.exp (L ^ 4) * Real.exp (-(L ^ 9)) :=
      mul_le_mul_of_nonneg_right hcoefficient (Real.exp_pos _).le
    _ = Real.exp (L ^ 4 - L ^ 9) := by rw [← Real.exp_add]; congr 1
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventually_deletion_comparison_error (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ b d q S V : ℝ,
      0 ≤ b → 0 ≤ d → 0 ≤ q →
      b ≤ Real.exp (C * Real.log L) → d ≤ Real.exp (2 * L) →
      q ≤ Real.exp (100 * L ^ 2) → 1 ≤ S → 1 ≤ V →
      ((3 * b * d * q + b * Real.exp (101 * L)) * Real.exp (-(L ^ 9))) /
        (S * V) ≤ Real.exp (-L ^ (9 / 10 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (max 4800 (C + 104))] with L hL
  intro b d q S V hb0 hd0 hq0 hb hd hq hS hV
  exact deletion_comparison_error_bound L C b d q S V
    ((le_max_left _ _).trans hL) hC ((le_max_right _ _).trans hL)
    hb0 hd0 hq0 hb hd hq hS hV

end TwoPointCorrelations

end OAI
