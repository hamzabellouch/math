import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.ZeroDensity.RetainedLowZeroEstimate

namespace OAI

/-! # The low-zero contribution at the actual growing conductor cutoff -/

namespace Ostmann
open Filter

theorem eventual_low_zero_error (C c a D : ℝ) (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ a * L * Real.exp ((9 / 10 : ℝ) * L) →
      2 * (C * (6 * q) ^ 13) ^ 2 *
        Real.exp (-(Real.exp L * (c / (Real.log 2 + 6 * q))) / 2) ≤
          Real.exp (-D * L) := by
  let b := 2 + 6 * a
  let E := max (D + 25) 1
  have hb : 0 < b := by dsimp [b]; linarith
  have hE : 0 < E := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hpoly := ((isLittleO_pow_exp_pos_mul_atTop 26
    (show (0 : ℝ) < 8 / 5 by norm_num)).const_mul_left (2 * C ^ 2 * (6 * a) ^ 26)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hfast := ((isLittleO_pow_exp_pos_mul_atTop 2
    (show (0 : ℝ) < 1 / 10 by norm_num)).const_mul_left (2 * b * E)).bound hc
  filter_upwards [hpoly, hfast, eventually_ge_atTop (1 : ℝ)] with L hpoly hfast hL
  intro q hq hqa
  have hLp : 0 < L := by linarith
  have hpoly' : 2 * C ^ 2 * (6 * a) ^ 26 * L ^ 26 ≤ Real.exp ((8 / 5 : ℝ) * L) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (2 * C ^ 2 * (6 * a) ^ 26) * L ^ 26),
      abs_of_pos (Real.exp_pos _), one_mul] using hpoly
  have hfast' : 2 * b * E * L ^ 2 ≤ c * Real.exp ((1 / 10 : ℝ) * L) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * b * E * L ^ 2),
      abs_of_pos (Real.exp_pos _)] using hfast
  have hden0 : 0 < Real.log 2 + 6 * q := by
    have hh : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hden : Real.log 2 + 6 * q ≤ b * L * Real.exp ((9 / 10 : ℝ) * L) := by
    have he : 1 ≤ Real.exp ((9 / 10 : ℝ) * L) := Real.one_le_exp (by positivity)
    have hprod : 1 ≤ L * Real.exp ((9 / 10 : ℝ) * L) :=
      hL.trans (le_mul_of_one_le_right hLp.le he)
    have hl : Real.log (2 : ℝ) ≤ 2 := Real.log_le_self (by norm_num)
    dsimp [b]
    nlinarith
  have hexp : Real.exp ((1 / 10 : ℝ) * L) * Real.exp ((9 / 10 : ℝ) * L) =
      Real.exp L := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hgap : E * L ≤ (Real.exp L * (c / (Real.log 2 + 6 * q))) / 2 := by
    have hm := mul_le_mul_of_nonneg_right hfast' (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    rw [mul_assoc c, hexp] at hm
    have hd := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 2 * E * L)
    have hf : (E * L) * (2 * (Real.log 2 + 6 * q)) ≤ Real.exp L * c := by
      nlinarith [hm, hd]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hden0).mpr
    convert hf using 1
    ring
  have hcoefficient : 2 * (C * (6 * q) ^ 13) ^ 2 ≤ Real.exp (25 * L) := by
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 6 * q)
      (show 6 * q ≤ 6 * (a * L * Real.exp ((9 / 10 : ℝ) * L)) by linarith [hqa]) 26
    have hm := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2 * C ^ 2)
    have hpowexp : Real.exp ((9 / 10 : ℝ) * L) ^ 26 =
        Real.exp ((117 / 5 : ℝ) * L) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hbnd : 2 * (C * (6 * q) ^ 13) ^ 2 ≤
        (2 * C ^ 2 * (6 * a) ^ 26 * L ^ 26) * Real.exp ((117 / 5 : ℝ) * L) := by
      convert hm using 1 <;> simp only [mul_pow, hpowexp] <;> ring
    calc
      _ ≤ _ := hbnd
      _ ≤ Real.exp ((8 / 5 : ℝ) * L) * Real.exp ((117 / 5 : ℝ) * L) :=
        mul_le_mul_of_nonneg_right hpoly' (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ Real.exp (25 * L) * Real.exp (-E * L) := mul_le_mul hcoefficient
      (Real.exp_le_exp.mpr (by linarith)) (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp ((25 - E) * L) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_right (le_max_left (D + 25) 1) hLp.le
      dsimp [E]
      linarith)

end Ostmann

end OAI
