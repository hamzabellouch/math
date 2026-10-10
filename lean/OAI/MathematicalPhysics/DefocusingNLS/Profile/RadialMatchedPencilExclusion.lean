import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedKernelDeterminant
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedWeakParameterLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilExclusion

namespace OAI

/-! A nonzero free matching determinant excludes nearby matched weak kernels.
The weights and pressure may be supplied by `radialMatched_penaltyFamily`. -/

open Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedPencil_eventually_kernel_zero
    (ell : ℕ) (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (hz₁ : z₀.val.1=0) (hz₀ : diskProfile (profileMatchingParameter z₀)=0)
    (R : ℝ) (hLR : radialShootingR (profileMatchingParameter z₀)<R)
    (F : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z₀)))
    (hmass : F.limitWeight.density=radialMatchedFreeMassFunction z₀)
    (ζ : ℕ → ℂ) (ζ₀ : ℂ) (hζ : Tendsto ζ atTop (𝓝 ζ₀))
    (hζ₀ : -(1/32 : ℝ)≤ζ₀.re)
    (B : ℕ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (B₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : Tendsto B atTop (𝓝 B₀))
    (hBoundary : B₀=spectralFluxBoundary R (radialMatchedFreeMassFunction z₀ R)
      (radialMatchedFreeTransportFunction z₀ R)
      (spectralGaugeRobin (radialShootingFreeExterior z₀ R) (deriv (radialShootingFreeExterior z₀) R)
        (spectralJetRobin
          (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z₀)) ζ₀ R)
          (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z₀)) ζ₀ R))))
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z₀)) ζ₀ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z₀)) ζ₀ R)) ≠ 0)
    (hD : spectralSlowDeterminant ell (radialShootingB (profileMatchingParameter z₀))
      ((radialShootingR (profileMatchingParameter z₀))^2/4) ζ₀ ≠ 0) :
    let hR := (radialMatchedCore_radius_pos z₀).trans hLR
    ∀ᶠ i in atTop, ∀ v, F.compactPencil ell hR i
      (radialMatchedWeakOperator (s i) ell (z i) (hX i) (hm i) R hR (ζ i) (B i)) v=v → v=0 := by
  let hR := (radialMatchedCore_radius_pos z₀).trans hLR
  let hc := radialMatchedFreeMassFunction_continuous s hs z z₀ hz hX hm
  apply F.compactPencil_eventually_kernel_zero ell (radialMatchedCore_radius_pos z₀) hLR
    (fun i => radialMatchedWeakOperator (s i) ell (z i) (hX i) (hm i) R hR (ζ i) (B i))
    (radialMatchedLimitWeakOperator ell z₀ hc R hR ζ₀ B₀)
    (radialMatchedWeakOperator_parameter_tendsto ell s hs z z₀ hz hX hm R hR ζ ζ₀ hζ B B₀ hB)
  intro v hv
  by_contra hne
  exact hD (radialMatchedLimit_kernel_slowDeterminant_of_boundary ell z₀ hz₁ hz₀ hc R hLR
    F hmass ζ₀ hζ₀ v hne hdet B₀ hBoundary hv)

end DefocusingNLS

end OAI
