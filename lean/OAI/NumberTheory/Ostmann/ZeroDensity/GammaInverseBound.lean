import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import OAI.NumberTheory.Ostmann.ZeroDensity.GammaStripBound

namespace OAI

/-! # A reciprocal Gamma bound from the reflection formula -/

namespace Ostmann

open Complex

theorem complex_sin_norm_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, norm_I, mul_one, norm_ofNat]
  have hp : ‖exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  have hm : ‖exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  calc
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 :=
      div_le_div_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add hp hm)) (by norm_num)
    _ = _ := by ring

theorem gamma_inv_reflection (z : ℂ) (hz' : z.re < 1) :
    (Complex.Gamma z)⁻¹ = Complex.Gamma (1 - z) * sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ) := by
  have hne : Complex.Gamma (1 - z) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  calc
    _ = Complex.Gamma (1 - z) * (Complex.Gamma z * Complex.Gamma (1 - z))⁻¹ := by
      simp [mul_inv_rev, hne]
    _ = _ := by
      rw [Complex.Gamma_mul_Gamma_one_sub]
      simp only [inv_div]
      ring

theorem gamma_inv_norm_bound (C : ℝ) (hC : 0 ≤ C) (z : ℂ)
    (hz' : z.re < 1) (hΓ : ‖Complex.Gamma (1 - z)‖ ≤ C) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ (C / Real.pi) * Real.exp (Real.pi * |z.im|) := by
  rw [gamma_inv_reflection z hz', norm_div, norm_mul,
    Complex.norm_of_nonneg Real.pi_pos.le]
  have hs : ‖sin ((Real.pi : ℂ) * z)‖ ≤ Real.exp (Real.pi * |z.im|) := by
    convert complex_sin_norm_le_exp ((Real.pi : ℂ) * z) using 1
    simp [abs_mul, abs_of_pos Real.pi_pos]
  calc
    _ ≤ C * Real.exp (Real.pi * |z.im|) / Real.pi := by
      gcongr
    _ = _ := by ring

end Ostmann

end OAI
