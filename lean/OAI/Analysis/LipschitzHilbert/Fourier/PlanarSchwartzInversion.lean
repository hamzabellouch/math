import OAI.Analysis.LipschitzHilbert.Trees.SourcePlanarPlancherel
import OAI.Analysis.LipschitzHilbert.Estimates.FrozenSlopeMultiplier

namespace OAI

/-! Fourier inversion on the actual product plane, and the frozen
multiplier identity for every planar Schwartz input. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert

/-- The planar transform remains Schwartz, with the product norm. -/
def planarFourierSchwartz (f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm (𝓕 (hilbertPlanarSchwartz f))

theorem planarFourierSchwartz_apply (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    planarFourierSchwartz f z=planarFourier f z :=
  fourier_hilbertPlanar_bridge f z

theorem planarFourier_integrable (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Integrable (planarFourier f) (volume.prod volume) := by
  have h : Integrable (planarFourierSchwartz f : ℝ×ℝ → ℂ) (volume.prod volume) :=
    (planarFourierSchwartz f).integrable
  simpa only [funext (planarFourierSchwartz_apply f)] using h

theorem planarFourier_inversion (f : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ×ℝ) :
    PacketRepresentation.planarInverse (planarFourier f) x=f x := by
  have hinv : (𝓕⁻ (𝓕 (hilbertPlanarSchwartz f) : SchwartzMap (WithLp 2 (ℝ×ℝ)) ℂ) :
      SchwartzMap (WithLp 2 (ℝ×ℝ)) ℂ)=hilbertPlanarSchwartz f :=
    FourierTransform.fourierInv_fourier_eq _
  have h := congrArg (fun g : SchwartzMap (WithLp 2 (ℝ×ℝ)) ℂ => g (WithLp.toLp 2 x)) hinv
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, integral_hilbertPlanar_bridge] at h
  simpa only [WithLp.prod_inner_apply, Real.inner_apply, fourier_hilbertPlanar_bridge,
    hilbertPlanarSchwartz_apply, PacketRepresentation.planarInverse, mul_comm] using h

theorem schwartz_frozen_slope_multiplier (k : ℝ → ℂ) (hk : Integrable k)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (u : ℝ×ℝ → ℝ) (x : ℝ×ℝ) :
    PacketRepresentation.slopeKernelOperator k u f x =
      ∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (𝓕 k (omega.1+u x*omega.2)*planarFourier f omega) ∂volume.prod volume := by
  have h := PacketRepresentation.frozen_slope_multiplier k (planarFourier f)
    hk (planarFourier_integrable f) u x
  simpa only [funext (planarFourier_inversion f)] using h

end LipschitzHilbert

end

end OAI
