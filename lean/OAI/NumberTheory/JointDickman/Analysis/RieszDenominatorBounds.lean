import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace OAI

/-! # Uniform integrable bounds for the Riesz--Perron denominator -/
namespace JointDickman

theorem rieszDenominator_im_lower_bound (s : ℂ) :
    s.im^2 ≤ ‖s‖*‖s+1‖ := by
  have h1 := Complex.abs_im_le_norm s
  have h2 : |s.im| ≤ ‖s+1‖ := by simpa using Complex.abs_im_le_norm (s+1)
  have h := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  nlinarith [sq_abs s.im]

theorem rieszDenominator_lower_bound {s : ℂ} (hs : 1/2 ≤ s.re) :
    (1+s.im^2)/5 ≤ ‖s‖*‖s+1‖ := by
  have h1 : (1/2:ℝ) ≤ ‖s‖ := hs.trans ((le_abs_self _).trans (Complex.abs_re_le_norm s))
  have h2 : (1/2:ℝ) ≤ ‖s+1‖ := by
    have h := Complex.abs_re_le_norm (s+1)
    have hle := le_abs_self (s+1).re
    simp only [Complex.add_re,Complex.one_re] at h hle
    linarith
  have hprod : (1/2:ℝ)*(1/2) ≤ ‖s‖*‖s+1‖ :=
    mul_le_mul h1 h2 (by norm_num) (norm_nonneg _)
  nlinarith [rieszDenominator_im_lower_bound s]

theorem rieszDenominator_inv_bound {s : ℂ} (hs : 1/2 ≤ s.re) :
    1/(‖s‖*‖s+1‖) ≤ 5/(1+s.im^2) := by
  have hp : 0 < (1+s.im^2)/5 := by positivity
  have h := one_div_le_one_div_of_le hp (rieszDenominator_lower_bound hs)
  convert h using 1; field_simp

end JointDickman

end OAI
