import OAI.Analysis.LipschitzHilbert.Fourier.LineKernelScaling
import OAI.Analysis.LipschitzHilbert.Fourier.DyadicSmoothCutoff

namespace OAI

/-! Exact kernel mass, cancellation, and uniform Lipschitz approximation
for the actual line projections. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_integral (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) :
    (∫ t, lineProjectionKernel q W hW t)=q 0 := by
  have he : (𝓕 (lineProjectionKernel q W hW) : SchwartzMap ℝ ℂ) 0=q 0 := by
    simp only [lineProjectionKernel,FourierTransform.fourier_fourierInv_eq,dilatedSlopeWindow_apply,mul_zero]
  rw [SchwartzMap.fourier_coe,Real.fourier_eq] at he
  simpa only [inner_zero_right,neg_zero,Real.fourierChar.map_zero_eq_one,one_smul] using he

theorem lineConvolution_centered_bound (K : SchwartzMap ℝ ℂ) (b : ℝ → ℂ)
    (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B) (L : ℝ)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x : ℝ) :
    ‖lineConvolution K b x-(∫ t, K t)*b x‖≤L*(∫ t, |t| *‖K t‖) := by
  have h1 := lineConvolution_integrand_of_bounded K b K.integrable hbm B hb x
  have he : lineConvolution K b x-(∫ t, K t)*b x=
      ∫ t, K t*(b (x-t)-b x) := by
    simp_rw [mul_sub]
    rw [integral_sub h1 (K.integrable.mul_const (b x)),integral_mul_const]
    rfl
  rw [he]
  have hn := norm_integral_le_of_norm_le
    ((schwartz_first_absolute_moment_integrable K).const_mul L)
    (Filter.Eventually.of_forall (fun t => show ‖K t*(b (x-t)-b x)‖≤L*(|t| *‖K t‖) from by
      rw [norm_mul]
      have hh := hLip (x-t) x
      simp only [sub_sub_cancel_left,abs_neg] at hh
      calc
        _ ≤ ‖K t‖*(L*|t|) := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
        _ = _ := by ring))
  simpa only [integral_const_mul] using hn

theorem lineProjection_centered_bound (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B)
    (L : ℝ) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x : ℝ) :
    ‖lineConvolution (lineProjectionKernel q W hW.ne') b x-q 0*b x‖≤
      L*W*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖) := by
  have hh := lineConvolution_centered_bound (lineProjectionKernel q W hW.ne') b hbm B hb L hLip x
  rw [lineProjectionKernel_integral,lineProjectionKernel_moment1 q W hW] at hh
  simpa only [mul_assoc] using hh

theorem dyadicProjection_lipschitz_bound (W : ℝ) (hW : 0<W)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B)
    (L : ℝ) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x : ℝ) :
    ‖lineConvolution (lineProjectionKernel dyadicDifference W hW.ne') b x‖≤
      L*W*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖) := by
  have hh := lineProjection_centered_bound dyadicDifference W hW b hbm B hb L hLip x
  simpa only [dyadicDifference_small 0 (by norm_num),zero_mul,sub_zero] using hh

theorem lowpassProjection_lipschitz_approximation (W : ℝ) (hW : 0<W)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hb : ∀ x, ‖b x‖≤B)
    (L : ℝ) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) (x : ℝ) :
    ‖lineConvolution (lineProjectionKernel reassemblyLow W hW.ne') b x-b x‖≤
      L*W*(∫ t, |t| *‖(𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t‖) := by
  have hh := lineProjection_centered_bound reassemblyLow W hW b hbm B hb L hLip x
  simpa only [reassemblyLow_one 0 (by norm_num),one_mul] using hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
