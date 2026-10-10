import Mathlib.Analysis.Real.Pi.Bounds
import OAI.NumberTheory.Ostmann.ZeroDensity.SharpGammaVertical

namespace OAI

/-! # The Gamma factor along the smoothed functional-equation contour -/

namespace Ostmann

open Complex

 theorem gammaReal_shift_quotient (z w : ℂ) :
    Complex.Gammaℝ (z + w) / Complex.Gammaℝ z =
      (Real.pi : ℂ) ^ (-w / 2) * (Complex.Gamma ((z + w) / 2) / Complex.Gamma (z / 2)) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def,
    show -(z + w) / 2 = -z / 2 + -w / 2 by ring, Complex.cpow_add _ _ hp,
    mul_assoc, mul_div_mul_left _ _ (Complex.cpow_ne_zero_iff.mpr (Or.inl hp)), mul_div_assoc]

 theorem sharp_gammaReal_shift (z w : ℂ)
    (hz : 1 / 4 ≤ z.re) (hz3 : z.re ≤ 3 / 2)
    (hw : 0 ≤ w.re) (hw2 : w.re ≤ 2) :
    ‖Complex.Gammaℝ (z + w) / Complex.Gammaℝ z‖ ≤
      Real.exp ((59 + |Real.eulerMascheroniConstant|) * (1 + |w.im|)) *
        (|z.im| + 2) ^ (w.re / 2) := by
  have he (s : ℂ) : ((s.re / 2 : ℝ) : ℂ) + (s.im / 2 : ℝ) * I = s / 2 := by
    apply Complex.ext <;> simp
  have he' : (((z.re / 2 + w.re / 2 : ℝ)) : ℂ) +
      ((z.im / 2 : ℝ) + (w.im / 2 : ℝ)) * I = (z + w) / 2 := by
    apply Complex.ext <;> simp <;> ring
  have hg := sharp_gamma_quotient (z.re / 2) (z.re / 2 + w.re / 2)
    (z.im / 2) (w.im / 2) (by linarith) (by linarith) (by linarith)
  rw [he', he, show z.re / 2 + w.re / 2 - z.re / 2 = w.re / 2 by ring] at hg
  have hp : ‖(Real.pi : ℂ) ^ (-w / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp only [div_ofNat_re, neg_re]
    linarith
  rw [gammaReal_shift_quotient, norm_mul, norm_div]
  calc
    _ ≤ 1 * (Real.exp ((59 + |Real.eulerMascheroniConstant|) * (w.re / 2 + |w.im / 2|)) *
        (|z.im / 2| + 2) ^ (w.re / 2)) := mul_le_mul hp hg (by positivity) (by norm_num)
    _ ≤ _ := by
      rw [one_mul]
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith [abs_nonneg w.im]
      · apply Real.rpow_le_rpow (by positivity)
        · rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          linarith [abs_nonneg z.im]
        · positivity
      · positivity
      · positivity

end Ostmann

end OAI
