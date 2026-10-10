import OAI.Analysis.LipschitzHilbert.Fourier.BoundedConvolutionComposition
import OAI.Analysis.LipschitzHilbert.Fourier.ProductPVLinear

namespace OAI

/-! The multiplier is linear in its Schwartz symbol on bounded measurable
inputs. The input need not have finite L2 norm. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineProjectionKernel_add (p q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) :
    lineProjectionKernel (p+q) W hW=lineProjectionKernel p W hW+lineProjectionKernel q W hW := by
  simp only [lineProjectionKernel,dilatedSlopeWindow,map_add,FourierTransform.fourierInv_add]

theorem lineProjectionKernel_smul (p : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) (c : ℂ) :
    lineProjectionKernel (c • p) W hW=c • lineProjectionKernel p W hW := by
  simp only [lineProjectionKernel,dilatedSlopeWindow,map_smul,FourierTransform.fourierInv_smul]

theorem lineProjectionKernel_dilate (p : SchwartzMap ℝ ℂ) (d W : ℝ) (hd : d≠0) (hW : W≠0) :
    lineProjectionKernel (dilatedSlopeWindow p d hd) W hW=
      lineProjectionKernel p (d*W) (mul_ne_zero hd hW) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineProjectionKernel (dilatedSlopeWindow p d hd) W hW) : SchwartzMap ℝ ℂ) eta=
    (𝓕 (lineProjectionKernel p (d*W) (mul_ne_zero hd hW)) : SchwartzMap ℝ ℂ) eta
  simp only [lineProjectionKernel,FourierTransform.fourier_fourierInv_eq,dilatedSlopeWindow_apply]
  rw [mul_assoc]

def boundedVerticalMultiplierLM (W : ℝ) (hW : 0<W) (f : (ℝ×ℝ) → ℂ)
    (hfm : Measurable f) (B : ℝ) (hf : ∀ z, ‖f z‖≤B) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] ((ℝ×ℝ) → ℂ) where
  toFun p := verticalConvolution (verticalProfileKernel p W 0) f
  map_add' p q := by
    funext z
    simp only [←lineProjectionKernel_eq_verticalProfile _ W hW,lineProjectionKernel_add]
    change (∫ t, (lineProjectionKernel p W hW.ne' t+lineProjectionKernel q W hW.ne' t)*
      f (z.1,z.2-t))=_
    simp_rw [add_mul]
    exact integral_add
      (lineConvolution_integrand_of_bounded _ _ (lineProjectionKernel p W hW.ne').integrable
        (hfm.comp (by fun_prop)) B (fun y => hf _) z.2)
      (lineConvolution_integrand_of_bounded _ _ (lineProjectionKernel q W hW.ne').integrable
        (hfm.comp (by fun_prop)) B (fun y => hf _) z.2)
  map_smul' c p := by
    funext z
    simp only [←lineProjectionKernel_eq_verticalProfile _ W hW,lineProjectionKernel_smul]
    change (∫ t, (c*lineProjectionKernel p W hW.ne' t)*f (z.1,z.2-t))=
      c*(∫ t, lineProjectionKernel p W hW.ne' t*f (z.1,z.2-t))
    simp_rw [mul_assoc]
    exact integral_const_mul c _

@[simp] theorem boundedVerticalMultiplierLM_apply (W : ℝ) (hW : 0<W) (f : (ℝ×ℝ) → ℂ)
    (hfm : Measurable f) (B : ℝ) (hf : ∀ z, ‖f z‖≤B) (p : SchwartzMap ℝ ℂ) :
    boundedVerticalMultiplierLM W hW f hfm B hf p=
      verticalConvolution (verticalProfileKernel p W 0) f := rfl

theorem verticalMultiplier_dilate (p : SchwartzMap ℝ ℂ) (d W : ℝ) (hd : 0<d) (hW : 0<W)
    (f : (ℝ×ℝ) → ℂ) :
    verticalConvolution (verticalProfileKernel (dilatedSlopeWindow p d hd.ne') W 0) f=
      verticalConvolution (verticalProfileKernel p (d*W) 0) f := by
  simp only [←lineProjectionKernel_eq_verticalProfile _ W hW,
    ←lineProjectionKernel_eq_verticalProfile _ (d*W) (mul_pos hd hW),lineProjectionKernel_dilate]

end LipschitzHilbert.PacketRepresentation

end

end OAI
