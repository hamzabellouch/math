import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalFluxLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFreeBoundaryAnalytic
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralJointUniformLimit

namespace OAI

/-! Local uniform convergence of the actual outgoing boundary operators. -/

open Filter Topology Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatchedCanonicalFlux_locallyUniform
    (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0) (ell : ℕ)
    (Y Z : ℕ → ℂ → ℝ → E₄)
    (hY : ∀ i, IsCanonicalHolomorphicColumn
      (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i))
      (s i+radialInnerShootingThreshold) (Real.log innerBoundaryRadius) (1,0) (Y i))
    (hZ : ∀ i, IsCanonicalHolomorphicColumn
      (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i))
      (s i+radialInnerShootingThreshold) (Real.log innerBoundaryRadius) (0,1) (Z i))
    (R : ℝ) (hR : innerBoundaryRadius < R)
    (hLR : radialShootingR (profileMatchingParameter z₀) < R)
    (U : Set ℂ) (hU : IsOpen U)
    (hhalf : ∀ lam ∈ U, -(1/32 : ℝ) ≤ lam.re)
    (hd : ∀ lam ∈ U, spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell
        (radialShootingB (profileMatchingParameter z₀)) lam R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell
        (radialShootingB (profileMatchingParameter z₀)) lam R)) ≠ 0) :
    TendstoLocallyUniformlyOn
      (fun i lam => radialMatchedCanonicalFlux (s i) (z i) R (Y i) (Z i) lam)
      (radialMatchedFreeBoundary ell z₀ R) atTop U := by
  apply spectral_locallyUniform_of_joint _ _ U hU
  · intro lam hlam
    exact (radialMatchedFreeBoundary_analyticAt ell z₀ R hLR lam
      (hhalf lam hlam) (hd lam hlam)).differentiableAt.continuousAt.continuousWithinAt
  · intro lam hlam
    exact radialMatchedCanonicalFlux_joint_tendsto s hs z z₀ hz hX hm ell Y Z hY hZ
      R hR lam (hhalf lam hlam) (hd lam hlam)

end DefocusingNLS

end OAI
