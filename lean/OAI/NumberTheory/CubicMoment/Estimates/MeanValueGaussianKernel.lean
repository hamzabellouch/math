import OAI.NumberTheory.CubicMoment.Estimates.MeanValueLogSpacing
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace OAI

/-! The Gaussian Fourier kernel for the mean value of the actual integer
norm Dirichlet polynomial. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def meanValueGaussianPhase (L u t : ℝ) : ℂ :=
  Complex.exp (-((t/L:ℝ):ℂ)^2)*Complex.exp (((u*t:ℝ):ℂ)*Complex.I)

lemma meanValueGaussianPhase_scale {L : ℝ} (hL : L ≠ 0) (u t : ℝ) :
    meanValueGaussianPhase L u t = meanValueGaussianPhase 1 (L*u) (t/L) := by
  have he : (L*u)*(t/L) = u*t := by field_simp
  simp only [meanValueGaussianPhase,div_one,he]

lemma meanValueGaussianPhase_one_integrable (u : ℝ) :
    Integrable (meanValueGaussianPhase 1 u) := by
  have he : meanValueGaussianPhase 1 u = fun t : ℝ =>
      Complex.exp (-(1:ℂ)*(t:ℂ)^2+((u:ℂ)*Complex.I)*(t:ℂ)+0) := by
    funext t
    simp only [meanValueGaussianPhase,div_one,← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  exact integrable_cexp_quadratic (b := (1:ℂ)) (by norm_num) _ _

lemma meanValueGaussianPhase_integrable {L : ℝ} (hL : 0 < L) (u : ℝ) :
    Integrable (meanValueGaussianPhase L u) := by
  have he : meanValueGaussianPhase L u = fun t => meanValueGaussianPhase 1 (L*u) (t/L) :=
    funext (meanValueGaussianPhase_scale hL.ne' u)
  rw [he]
  exact (meanValueGaussianPhase_one_integrable (L*u)).comp_div hL.ne'

lemma meanValueGaussianPhase_one_integral_norm (u : ℝ) :
    ‖∫ t : ℝ, meanValueGaussianPhase 1 u t‖ =
      Real.sqrt Real.pi*Real.exp (-u^2/4) := by
  have he : (∫ t : ℝ, meanValueGaussianPhase 1 u t) =
      (Real.pi/(1:ℂ))^(1/2:ℂ)*Complex.exp (-(u:ℂ)^2/(4*(1:ℂ))) := by
    convert fourierIntegral_gaussian (b := (1:ℂ)) (by norm_num) (u:ℂ) using 1
    congr 1
    funext t
    simp only [meanValueGaussianPhase,div_one]
    rw [mul_comm]
    congr 1 <;> push_cast <;> ring_nf
  rw [he,norm_mul]
  have hp : ‖(Real.pi/(1:ℂ))^(1/2:ℂ)‖ = Real.sqrt Real.pi := by
    rw [div_one,show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num,
      Complex.norm_cpow_real,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
      ← Real.sqrt_eq_rpow]
  have ht : -(u:ℂ)^2/(4*(1:ℂ)) = ((-u^2/4:ℝ):ℂ) := by push_cast; ring
  rw [hp,ht,Complex.norm_exp,Complex.ofReal_re]

lemma meanValueGaussianPhase_integral_norm {L : ℝ} (hL : 0 < L) (u : ℝ) :
    ‖∫ t : ℝ, meanValueGaussianPhase L u t‖ =
      L*Real.sqrt Real.pi*Real.exp (-(L*u)^2/4) := by
  have he : meanValueGaussianPhase L u = fun t => meanValueGaussianPhase 1 (L*u) (t/L) :=
    funext (meanValueGaussianPhase_scale hL.ne' u)
  rw [he,Measure.integral_comp_div,norm_smul,Real.norm_eq_abs,abs_of_pos hL,
    meanValueGaussianPhase_one_integral_norm]
  rw [abs_of_pos hL]
  ring

end CubicFirstMoment

end

end OAI
