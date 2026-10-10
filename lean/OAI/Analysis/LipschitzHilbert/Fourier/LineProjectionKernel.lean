import OAI.Analysis.LipschitzHilbert.Fourier.LineFrequencyProjection

namespace OAI

/-! The line Fourier projection is the actual convolution with its
inverse-Fourier kernel. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ENNReal
namespace LipschitzHilbert.PacketRepresentation

def lineProjectionKernel (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (dilatedSlopeWindow q W hW)

theorem lineSchwartzProjection_eq_convolution (q : SchwartzMap ℝ ℂ)
    (W : ℝ) (hW : W≠0) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    lineSchwartzProjection q W hW f x=lineConvolution (lineProjectionKernel q W hW) f x := by
  have he : lineSchwartzProjection q W hW f=
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (lineProjectionKernel q W hW) f := by
    apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
    ext eta
    change (𝓕 (lineSchwartzProjection q W hW f)) eta=
      (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (lineProjectionKernel q W hW) f)) eta
    rw [lineSchwartzProjection_fourier,SchwartzMap.fourier_convolution]
    simp only [SchwartzMap.pairing_apply_apply,lineProjectionKernel,
      FourierTransform.fourier_fourierInv_eq,dilatedSlopeWindow_apply,ContinuousLinearMap.mul_apply']
  rw [he,SchwartzMap.convolution_apply,convolution_def]
  rfl

theorem lineConvolution_integrand_of_bounded (K f : ℝ → ℂ)
    (hK : Integrable K) (hfm : Measurable f) (B : ℝ) (hB : ∀ x, ‖f x‖≤B) (x : ℝ) :
    Integrable (fun t => K t*f (x-t)) := by
  apply (hK.norm.mul_const B).mono'
    (hK.aestronglyMeasurable.mul (hfm.comp (by fun_prop)).aestronglyMeasurable)
  filter_upwards [] with t
  change ‖K t*f (x-t)‖≤‖K t‖*B
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)

theorem lineConvolution_sub_of_bounded (K f g : ℝ → ℂ)
    (hK : Integrable K) (hfm : Measurable f) (hgm : Measurable g)
    (Bf Bg : ℝ) (hf : ∀ x, ‖f x‖≤Bf) (hg : ∀ x, ‖g x‖≤Bg) :
    lineConvolution K (f-g)=lineConvolution K f-lineConvolution K g := by
  funext x
  unfold lineConvolution
  simp only [Pi.sub_apply,mul_sub]
  exact integral_sub (lineConvolution_integrand_of_bounded K f hK hfm Bf hf x)
    (lineConvolution_integrand_of_bounded K g hK hgm Bg hg x)

end LipschitzHilbert.PacketRepresentation

end

end OAI
