import OAI.Analysis.FiniteFactor.CrossedProduct.AngleLaw
import OAI.Analysis.FiniteFactor.PeriodizedUniform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- Direct integral estimate for a real nonzero frequency on an interval. -/
theorem norm_interval_fourier_le (a b w : ℝ) (hw : w ≠ 0) :
    ‖∫ t in a..b, Complex.exp ((w : ℂ) * Complex.I * t)‖ ≤ 2 / |w| := by
  rw [integral_exp_mul_complex (mul_ne_zero (Complex.ofReal_ne_zero.mpr hw) Complex.I_ne_zero),
    norm_div, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg w)
  calc
    _ ≤ ‖Complex.exp ((w : ℂ) * Complex.I * b)‖ +
        ‖Complex.exp ((w : ℂ) * Complex.I * a)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- The actual normalized angle interval, before reducing phases modulo one. -/
theorem sourceAngle_fourier_le (i : SourceCoordinate) (w : ℝ) (hw : w ≠ 0) :
    ‖∫ t, Complex.exp ((w : ℂ) * Complex.I * t) ∂sourceAngleMarginal i‖ ≤
      2 / (sourceAngleUnit i * |w|) := by
  have ha := sourceAngleUnit_pos i
  rw [sourceAngleMarginal, sourceAngleInterval, cond_closed_interval_eq,
    ProbabilityTheory.cond, integral_smul_measure, Real.volume_Ioc]
  rw [show 2 * sourceAngleUnit i - sourceAngleUnit i = sourceAngleUnit i by ring]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal ha.le, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  rw [← intervalIntegral.integral_of_le (show sourceAngleUnit i ≤ 2*sourceAngleUnit i by linarith)]
  calc
    _ ≤ (sourceAngleUnit i)⁻¹ * (2 / |w|) :=
      mul_le_mul_of_nonneg_left (norm_interval_fourier_le _ _ w hw) (inv_nonneg.mpr ha.le)
    _ = _ := by ring

/-- Integer frequencies do not see the integer part of a phase. -/
theorem fourier_fract (v : ℤ) (t : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((v : ℂ) * (Int.fract t : ℝ))) =
      Complex.exp (2 * Real.pi * Complex.I * ((v : ℂ) * (t : ℂ))) := by
  rw [Int.fract]
  push_cast
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((v : ℂ) * ((t : ℂ) - (⌊t⌋ : ℂ))) =
      2 * Real.pi * Complex.I * ((v : ℂ) * (t : ℂ)) +
        ((-(v * ⌊t⌋) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The two actual phases have the Fourier transform of the combined frequency. -/
theorem pair_fourier_fract (v v' : ℤ) (n n' t : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((v : ℂ) * (Int.fract (n*t) : ℝ) + (v' : ℂ) * (Int.fract (n'*t) : ℝ))) =
    Complex.exp (((2 * Real.pi * ((v : ℝ)*n + (v' : ℝ)*n') : ℝ) : ℂ) * Complex.I * t) := by
  rw [mul_add, Complex.exp_add, fourier_fract, fourier_fract, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sourceAngle_pair_fourier_le (i : SourceCoordinate) (v v' : ℤ) (n n' : ℝ)
    (hw : (v : ℝ)*n + (v' : ℝ)*n' ≠ 0) :
    ‖∫ t, Complex.exp (2 * Real.pi * Complex.I *
      ((v : ℂ) * (Int.fract (n*t) : ℝ) + (v' : ℂ) * (Int.fract (n'*t) : ℝ)))
      ∂sourceAngleMarginal i‖ ≤
      1 / (Real.pi * sourceAngleUnit i * |(v : ℝ)*n + (v' : ℝ)*n'|) := by
  simp_rw [pair_fourier_fract]
  have hp := sourceAngle_fourier_le i (2*Real.pi*((v : ℝ)*n+(v' : ℝ)*n'))
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw)
  convert hp using 1
  rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  norm_num
  ring

end
end FiniteFactor

end OAI
