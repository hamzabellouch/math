import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinPlateau
import OAI.Analysis.LipschitzHilbert.Fourier.FiniteBandMultiplier
import Mathlib.Analysis.Fourier.Convolution

namespace OAI

/-! Exact modulated convolution kernels for the fixed vertical bin
profiles, with a uniform L1 norm at every width and carrier. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def modulatedTimeKernel (K : ℝ → ℂ) (W center : ℝ) (t : ℝ) : ℂ :=
  Real.fourierChar (center*t) • scaledTimeKernel K W t

theorem modulatedTimeKernel_integrable (K : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    Integrable (modulatedTimeKernel K W center) := by
  have hi := scaledTimeKernel_integrable K K.integrable W hW.ne'
  apply hi.norm.mono'
    ((show Continuous (fun t : ℝ => Real.fourierChar (center*t)) by fun_prop).aestronglyMeasurable.smul
      hi.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t => le_of_eq (Circle.norm_smul _ _))

theorem modulatedTimeKernel_fourier (K : ℝ → ℂ) (W center eta : ℝ) (hW : 0<W) :
    𝓕 (modulatedTimeKernel K W center) eta=𝓕 K (W*(eta-center)) := by
  rw [←scaledTimeKernel_fourier K W hW (eta-center)]
  rw [Real.fourier_eq,Real.fourier_eq]
  simp only [Real.inner_apply,modulatedTimeKernel]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [←mul_smul,←Real.fourierChar.map_add_eq_mul]
  congr 2
  ring

theorem modulatedTimeKernel_norm (K : ℝ → ℂ) (W center t : ℝ) (hW : 0<W) :
    ‖modulatedTimeKernel K W center t‖=W⁻¹*‖K (t/W)‖ := by
  rw [modulatedTimeKernel,Circle.norm_smul,scaledTimeKernel,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg hW.le]

theorem modulatedTimeKernel_l1 (K : SchwartzMap ℝ ℂ) (W center : ℝ) (hW : 0<W) :
    (∫ t, ‖modulatedTimeKernel K W center t‖)=∫ t, ‖K t‖ := by
  simp_rw [modulatedTimeKernel_norm K W center _ hW]
  rw [integral_const_mul,Measure.integral_comp_div (fun t => ‖K t‖) W,
    abs_of_pos hW,smul_eq_mul]
  rw [←mul_assoc,inv_mul_cancel₀ hW.ne',one_mul]

def verticalProfileKernel (q : SchwartzMap ℝ ℂ) (W center : ℝ) : ℝ → ℂ :=
  modulatedTimeKernel (𝓕⁻ q : SchwartzMap ℝ ℂ) W center

theorem verticalProfileKernel_fourier (q : SchwartzMap ℝ ℂ) (W center eta : ℝ) (hW : 0<W) :
    𝓕 (verticalProfileKernel q W center) eta=q (W*(eta-center)) := by
  rw [verticalProfileKernel,modulatedTimeKernel_fourier _ W center eta hW]
  have h : (𝓕 (𝓕⁻ q : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=q := fourier_fourierInv_eq q
  exact congrArg (fun f : SchwartzMap ℝ ℂ => f (W*(eta-center))) h

def verticalConvolution (K : ℝ → ℂ) (f : ℝ×ℝ → ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ t, K t*f (z.1,z.2-t)

theorem verticalConvolution_uniform_bound (K : ℝ → ℂ) (hK : Integrable K)
    (f : ℝ×ℝ → ℂ) (C : ℝ) (hf : ∀ z, ‖f z‖≤C) (z : ℝ×ℝ) :
    ‖verticalConvolution K f z‖≤C*∫ t, ‖K t‖ := by
  have h := norm_integral_le_of_norm_le (hK.norm.const_mul C)
    (Filter.Eventually.of_forall (fun t => show ‖K t*f (z.1,z.2-t)‖≤C*‖K t‖ from by
      rw [norm_mul,mul_comm C]
      exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)))
  simpa only [verticalConvolution,integral_const_mul] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
