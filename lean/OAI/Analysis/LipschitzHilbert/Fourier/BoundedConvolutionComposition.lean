import OAI.Analysis.LipschitzHilbert.Fourier.LineKernelScaling
import OAI.Analysis.LipschitzHilbert.Fourier.LineProjectionKernel

namespace OAI

/-! Composition and multiplier absorption for bounded inputs, before any
L2 membership of the input is known. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_assoc_bounded (K L : SchwartzMap ℝ ℂ) (f : ℝ → ℂ)
    (hfm : Measurable f) (B : ℝ) (hf : ∀ x, ‖f x‖≤B) (x : ℝ) :
    lineConvolution K (lineConvolution L f) x=
      lineConvolution (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) K L) f x := by
  let M := ContinuousLinearMap.mul ℂ ℂ
  have hK : Integrable K := K.integrable
  have hL : Integrable L := L.integrable
  have hfg := hK.ae_convolution_exists M hL
  have hgk : ∀ᵐ y : ℝ, ConvolutionExistsAt L f y M volume := by
    exact Filter.Eventually.of_forall (lineConvolution_integrand_of_bounded L f hL hfm B hf)
  have hi : Integrable (fun p : ℝ×ℝ => (K p.2*L (p.1-p.2))*f (x-p.1)) := by
    apply (hK.convolution_integrand M hL).mul_bdd (c:=B)
    · exact (hfm.comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => hf (x-p.1))
  have ha := convolution_assoc' M M M M (fun a b c => mul_assoc a b c) hfg hgk
    (hi.congr (Filter.Eventually.of_forall (fun p => mul_assoc (K p.2) (L (p.1-p.2)) (f (x-p.1)))))
  simpa only [lineConvolution,SchwartzMap.convolution_apply,convolution_def,M,ContinuousLinearMap.mul_apply'] using ha.symm

theorem lineKernel_absorb (p q : SchwartzMap ℝ ℂ)
    (hpq : ∀ x, p x*q x=q x) (W : ℝ) (hW : W≠0) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (lineProjectionKernel p W hW) (lineProjectionKernel q W hW)=lineProjectionKernel q W hW := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (lineProjectionKernel p W hW) (lineProjectionKernel q W hW)) : SchwartzMap ℝ ℂ) eta=
    (𝓕 (lineProjectionKernel q W hW) : SchwartzMap ℝ ℂ) eta
  simp only [SchwartzMap.fourier_convolution,SchwartzMap.pairing_apply_apply,
    ContinuousLinearMap.mul_apply',lineProjectionKernel,FourierTransform.fourier_fourierInv_eq,
    dilatedSlopeWindow_apply,hpq]

theorem lineProjection_bounded_absorb (p q : SchwartzMap ℝ ℂ)
    (hpq : ∀ x, p x*q x=q x) (W : ℝ) (hW : W≠0)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hf : ∀ x, ‖f x‖≤B) (x : ℝ) :
    lineConvolution (lineProjectionKernel p W hW)
      (lineConvolution (lineProjectionKernel q W hW) f) x=
      lineConvolution (lineProjectionKernel q W hW) f x := by
  rw [lineConvolution_assoc_bounded _ _ f hfm B hf,lineKernel_absorb p q hpq]

theorem lineProjectionKernel_eq_verticalProfile (p : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    (lineProjectionKernel p W hW.ne' : ℝ → ℂ)=verticalProfileKernel p W 0 := by
  funext x
  rw [lineProjectionKernel_eq_scaled p W hW,scaledSchwartzKernel_apply]
  simp only [verticalProfileKernel,modulatedTimeKernel,zero_mul,
    Real.fourierChar.map_zero_eq_one,one_smul]

theorem verticalProjection_bounded_absorb (p q : SchwartzMap ℝ ℂ)
    (hpq : ∀ x, p x*q x=q x) (W : ℝ) (hW : 0<W)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (B : ℝ) (hf : ∀ z, ‖f z‖≤B) (z : ℝ×ℝ) :
    verticalConvolution (verticalProfileKernel p W 0)
      (verticalConvolution (verticalProfileKernel q W 0) f) z=
      verticalConvolution (verticalProfileKernel q W 0) f z := by
  have hslice : Measurable (fun y : ℝ => f (z.1,y)) := hfm.comp (by fun_prop)
  have h := lineProjection_bounded_absorb p q hpq W hW.ne'
    (fun y => f (z.1,y)) hslice B (fun y => hf _) z.2
  simp only [lineProjectionKernel_eq_verticalProfile p W hW,
    lineProjectionKernel_eq_verticalProfile q W hW] at h
  exact h

end LipschitzHilbert.PacketRepresentation

end

end OAI
