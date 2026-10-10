import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinAdjoint

namespace OAI

/-! The bin adjoint identity for the actual physical convolution pairings. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem physicalBin_adjoint (J : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ)
    (f g : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 planeMeasure) (hg : MemLp g 2 planeMeasure) :
    (∫ z, verticalConvolution (verticalProfileKernel verticalBinProfile W
        (verticalBinCenter J W n)) f z*star (g z) ∂planeMeasure)=
      ∫ z, f z*star (verticalConvolution (verticalProfileKernel verticalBinProfile W
        (verticalBinCenter J W n)) g z) ∂planeMeasure := by
  let K := verticalProfileKernel verticalBinProfile W (verticalBinCenter J W n)
  have hKi : Integrable K := verticalProfileKernel_integrable _ W _ hW
  have hKm : Measurable K := (verticalProfileKernel_continuous _ W _).measurable
  have h := verticalBinLp_adjoint J W hW n (hg.toLp g) (hf.toLp f)
  change inner ℂ (verticalConvolutionLp K hKi hKm (hg.toLp g)) (hf.toLp f)=
    inner ℂ (hg.toLp g) (verticalConvolutionLp K hKi hKm (hf.toLp f)) at h
  rw [verticalConvolutionLp_toLp K hKi hKm g hgm hg,
    verticalConvolutionLp_toLp K hKi hKm f hfm hf,
    memLp_inner_integral,memLp_inner_integral] at h
  simpa only [K,RCLike.inner_apply,starRingEnd_apply,mul_comm] using h.symm

end LipschitzHilbert.PacketRepresentation

end

end OAI
