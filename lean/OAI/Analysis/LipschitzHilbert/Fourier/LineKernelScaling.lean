import OAI.Analysis.LipschitzHilbert.Packets.LineConvolutionFrame
import OAI.Analysis.LipschitzHilbert.Fourier.FiniteTimeKernelMoment

namespace OAI

/-! The actual line projection kernel has the expected physical scale,
including its exact first absolute moment. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def scaledSchwartzKernel (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) : SchwartzMap ℝ ℂ :=
  (W:ℂ)⁻¹ • dilatedSlopeWindow (𝓕⁻ q) W⁻¹ (inv_ne_zero hW.ne')

theorem scaledSchwartzKernel_apply (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) (x : ℝ) :
    scaledSchwartzKernel q W hW x=scaledTimeKernel (𝓕⁻ q : SchwartzMap ℝ ℂ) W x := by
  simp only [scaledSchwartzKernel,smul_apply,smul_eq_mul,dilatedSlopeWindow_apply,scaledTimeKernel]
  congr 2
  ring

theorem lineProjectionKernel_eq_scaled (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    lineProjectionKernel q W hW.ne'=scaledSchwartzKernel q W hW := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineProjectionKernel q W hW.ne')) eta=(𝓕 (scaledSchwartzKernel q W hW)) eta
  simp only [lineProjectionKernel,FourierTransform.fourier_fourierInv_eq,dilatedSlopeWindow_apply]
  have he : (scaledSchwartzKernel q W hW : ℝ → ℂ)=
      scaledTimeKernel (𝓕⁻ q : SchwartzMap ℝ ℂ) W := funext (scaledSchwartzKernel_apply q W hW)
  rw [SchwartzMap.fourier_coe,he,scaledTimeKernel_fourier _ W hW]
  have hq : (𝓕 (𝓕⁻ q : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=q :=
    FourierTransform.fourier_fourierInv_eq q
  exact (congrArg (fun p : SchwartzMap ℝ ℂ => p (W*eta)) hq).symm

theorem lineProjectionKernel_moment1 (q : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    (∫ t, |t| *‖lineProjectionKernel q W hW.ne' t‖)=
      W*(∫ t, |t| *‖(𝓕⁻ q : SchwartzMap ℝ ℂ) t‖) := by
  have he (t : ℝ) : lineProjectionKernel q W hW.ne' t=
      scaledTimeKernel (𝓕⁻ q : SchwartzMap ℝ ℂ) W t := by
    rw [lineProjectionKernel_eq_scaled]
    exact scaledSchwartzKernel_apply q W hW t
  simp_rw [he]
  exact scaledTimeKernel_moment1 (𝓕⁻ q) W hW

end LipschitzHilbert.PacketRepresentation

end

end OAI
