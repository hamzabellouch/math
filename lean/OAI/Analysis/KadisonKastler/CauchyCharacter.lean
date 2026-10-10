import OAI.Analysis.KadisonKastler.CauchyFourier

namespace OAI

/-! # The characteristic function of the Cauchy density

The frequency is expressed in radians, matching the characters used by
the modular comparison. Fourier inversion accounts for the `2*pi` change
from mathlib's Fourier convention.
-/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory
open scoped FourierTransform

noncomputable section

private theorem laplaceKernel_rescale (γ s : ℝ) :
    laplaceKernel (2 * Real.pi * γ) (s / (2 * Real.pi)) =
      (Real.exp (-γ * |s|) : ℂ) := by
  rw [laplaceKernel, Complex.ofReal_exp]
  have hp : 0 < 2 * Real.pi := by positivity
  rw [abs_div, abs_of_pos hp]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The centered Cauchy characteristic function in the radian convention. -/
theorem integral_cauchyPDFReal_character_zero {γ : NNReal} (hγ : 0 < γ) (s : ℝ) :
    (∫ x : ℝ, (cauchyPDFReal 0 γ x : ℂ) * (Circle.exp (s * x) : ℂ)) =
      (Real.exp (-(γ : ℝ) * |s|) : ℂ) := by
  have h := fourierInv_cauchyPDFReal hγ (s / (2 * Real.pi))
  have harg (x : ℝ) : 2 * Real.pi * (x * (s / (2 * Real.pi))) = s * x := by
    field_simp [Real.pi_ne_zero]
  have hi : (∫ x : ℝ, (Circle.exp (s * x) : ℂ) * (cauchyPDFReal 0 γ x : ℂ)) =
      laplaceKernel (2 * Real.pi * γ) (s / (2 * Real.pi)) := by
    simpa only [Real.fourierInv_eq, Real.inner_apply, Circle.smul_def,
      Real.fourierChar_apply', harg, smul_eq_mul] using h
  calc
    _ = ∫ x : ℝ, (Circle.exp (s * x) : ℂ) * (cauchyPDFReal 0 γ x : ℂ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => mul_comm _ _
    _ = _ := hi.trans (laplaceKernel_rescale γ s)

/-- Translation of the density gives the phase factor for an arbitrary
center. -/
theorem integral_cauchyPDFReal_character {γ : NNReal} (hγ : 0 < γ) (t s : ℝ) :
    (∫ x : ℝ, (cauchyPDFReal t γ x : ℂ) * (Circle.exp (s * x) : ℂ)) =
      (Real.exp (-(γ : ℝ) * |s|) : ℂ) * (Circle.exp (s * t) : ℂ) := by
  rw [← integral_add_right_eq_self
    (fun x : ℝ => (cauchyPDFReal t γ x : ℂ) * (Circle.exp (s * x) : ℂ)) t]
  have hpdf (x : ℝ) : cauchyPDFReal t γ (x + t) = cauchyPDFReal 0 γ x := by
    simp only [cauchyPDFReal_def, add_sub_cancel_right, sub_zero]
  simp_rw [hpdf, mul_add, Circle.exp_add, Circle.coe_mul, ← mul_assoc]
  rw [integral_mul_const, integral_cauchyPDFReal_character_zero hγ]

end

end KadisonKastler

end OAI
