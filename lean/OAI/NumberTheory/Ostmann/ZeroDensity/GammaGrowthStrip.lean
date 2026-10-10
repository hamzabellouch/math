import Mathlib.Analysis.Real.Pi.Bounds
import OAI.NumberTheory.Ostmann.ZeroDensity.GammaRealContourBound

namespace OAI

/-! # Gamma-factor growth in the narrow strip around the contour

The upper bounds use only Euler's integral and reflection. They are needed
for the horizontal-edge logarithmic-derivative estimate.
-/

namespace Ostmann

open Complex

theorem gammaReal_inverse_eq (s : ℂ) :
    (Complex.Gammaℝ s)⁻¹ = (Real.pi : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2))⁻¹ := by
  rw [Complex.Gammaℝ_def, mul_inv]
  congr 1
  rw [← Complex.cpow_neg]
  congr 1
  ring

theorem gammaReal_growth_bounds : ∃ C : ℝ, 0 < C ∧
    (∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ 11 / 4 → ‖Complex.Gammaℝ s‖ ≤ C) ∧
    (∀ s : ℂ, -(3 / 4 : ℝ) ≤ s.re → s.re ≤ 3 / 2 →
      ‖(Complex.Gammaℝ s)⁻¹‖ ≤ C * Real.exp (Real.pi * |s.im|)) := by
  obtain ⟨C, hC, hΓ⟩ := gamma_positive_strip_bound (1 / 4) (11 / 8) (by norm_num)
  refine ⟨C, hC, ?_, ?_⟩
  · intro s hs hs'
    have hg := hΓ (s / 2) (by simp; linarith) (by simp; linarith)
    have hp : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
      simp
      linarith
    rw [Complex.Gammaℝ_def, norm_mul]
    exact (mul_le_mul hp hg (norm_nonneg _) (by norm_num)).trans_eq (one_mul C)
  · intro s hs hs'
    have hg := hΓ (1 - s / 2) (by simp; linarith) (by simp; linarith)
    have hi := gamma_inv_norm_bound C hC.le (s / 2) (by simp; linarith) hg
    have hp : ‖(Real.pi : ℂ) ^ (s / 2)‖ ≤ Real.pi := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      calc
        _ ≤ Real.pi ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi) (by simp; linarith)
        _ = _ := Real.rpow_one _
    have him : |(s / 2).im| ≤ |s.im| := by
      simp only [div_ofNat_im, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_nonneg s.im]
    rw [gammaReal_inverse_eq, norm_mul]
    calc
      _ ≤ Real.pi * ((C / Real.pi) * Real.exp (Real.pi * |(s / 2).im|)) :=
        mul_le_mul hp hi (norm_nonneg _) Real.pi_pos.le
      _ = C * Real.exp (Real.pi * |(s / 2).im|) := by field_simp
      _ ≤ C * Real.exp (Real.pi * |s.im|) := by gcongr

end Ostmann

end OAI
