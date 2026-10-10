import OAI.Analysis.LipschitzHilbert.Fourier.LineKernelCancellation
import OAI.Analysis.LipschitzHilbert.Fourier.LineKernelDecay

namespace OAI

/-! Smooth line projection preserves a Lipschitz bound uniformly in its
scale, up to the fixed kernel L1 norm. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_l1 (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    (∫ t, ‖lineProjectionKernel q W hW.ne' t‖)=∫ t, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖ := by
  simp_rw [lineProjectionKernel_norm q W hW]
  rw [integral_const_mul,Measure.integral_comp_div (fun t => ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖) W,
    abs_of_pos hW,smul_eq_mul,←mul_assoc,inv_mul_cancel₀ hW.ne',one_mul]

theorem lineConvolution_lipschitz (K : SchwartzMap ℝ ℂ) (b : ℝ → ℂ)
    (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B) (L : ℝ)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x y : ℝ) :
    ‖lineConvolution K b x-lineConvolution K b y‖≤
      (L*(∫ t, ‖K t‖))*|x-y| := by
  have h1 := lineConvolution_integrand_of_bounded K b K.integrable hbm B hb x
  have h2 := lineConvolution_integrand_of_bounded K b K.integrable hbm B hb y
  have he : lineConvolution K b x-lineConvolution K b y=
      ∫ t, K t*(b (x-t)-b (y-t)) := by
    simp_rw [mul_sub]
    rw [integral_sub h1 h2]
    rfl
  rw [he]
  have hh := norm_integral_le_of_norm_le (μ:=volume) (K.integrable.norm.const_mul (L*|x-y|))
    (Filter.Eventually.of_forall (fun t => show ‖K t*(b (x-t)-b (y-t))‖≤L*|x-y| *‖K t‖ from by
      rw [norm_mul]
      have hl := hLip (x-t) (y-t)
      rw [sub_sub_sub_cancel_right] at hl
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hl (norm_nonneg (K t))))
  rw [integral_const_mul] at hh
  convert hh using 1; ring

theorem lineProjection_lipschitz (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B) (L : ℝ)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x y : ℝ) :
    ‖lineConvolution (lineProjectionKernel q W hW.ne') b x-
      lineConvolution (lineProjectionKernel q W hW.ne') b y‖≤
      (L*(∫ t, ‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖))*|x-y| := by
  have hh := lineConvolution_lipschitz (lineProjectionKernel q W hW.ne') b hbm B hb L hLip x y
  rw [lineProjectionKernel_l1 q W hW] at hh
  exact hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
