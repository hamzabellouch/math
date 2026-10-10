import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalRobinJoint
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedBoundaryJoint
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSimpleKernel
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMovingParameterLimit

namespace OAI

/-! Actual gauge and flux factors preserve joint canonical Robin convergence. -/

open Filter Topology Set
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def radialMatchedCanonicalFlux (n : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (Y Z : ℂ → ℝ → E₄) (lam : ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  radialMatchedFluxBoundary n z R
      (spectralJetRobin
        (spectralPhysicalPair (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
          (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Y lam) R)
        (spectralPhysicalPair (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
          (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Z lam) R))

theorem radialMatchedCanonicalFlux_joint_tendsto
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
    (lam₀ : ℂ) (hlam₀ : -(1/32 : ℝ) ≤ lam₀.re)
    (hd : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell
        (radialShootingB (profileMatchingParameter z₀)) lam₀ R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell
        (radialShootingB (profileMatchingParameter z₀)) lam₀ R)) ≠ 0) :
    Tendsto (fun p : ℕ × ℂ => radialMatchedCanonicalFlux (s p.1) (z p.1) R (Y p.1) (Z p.1) p.2)
      (atTop ×ˢ 𝓝 lam₀) (𝓝 (radialMatchedFreeBoundary ell z₀ R lam₀)) := by
  have hj := radialMatchedCanonicalRobin_joint_tendsto s hs z z₀ hz ell Y Z hY hZ R hR lam₀ hlam₀ hd
  let M := fun i lam => spectralJetRobin
    (spectralPhysicalPair (radialShootingNu (s i+radialInnerShootingThreshold) (z i)-2*lam)
      (star (radialShootingNu (s i+radialInnerShootingThreshold) (z i))-2*lam) (Y i lam) R)
    (spectralPhysicalPair (radialShootingNu (s i+radialInnerShootingThreshold) (z i)-2*lam)
      (star (radialShootingNu (s i+radialInnerShootingThreshold) (z i))-2*lam) (Z i lam) R)
  let M₀ := spectralJetRobin
    (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z₀)) lam₀ R)
    (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z₀)) lam₀ R)
  have hh := radialMatchedBoundaryOperator_joint_tendsto s hs z z₀ hz hX hm R hR lam₀ M M₀ hj
  simpa only [radialMatchedCanonicalFlux,radialMatchedFreeBoundary,M,M₀] using hh

end DefocusingNLS

end OAI
