import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralCanonicalKernel
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalRobinAnalytic

namespace OAI

/-! Canonical boundary data for a regular radial mode, including its parameter derivative. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialSpectralMode_canonical_boundary_data (n ell N : ℕ) (hN : 7 ≤ N)
    (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : innerBoundaryRadius < R)
    (lam : ℂ) (hhalf : -(1/32 : ℝ) ≤ lam.re)
    (u : RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) N (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam)
    (Y Z : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1,0) Y)
    (hZ : IsCanonicalHolomorphicColumn (radialShootingNu (n+radialInnerShootingThreshold) z)
      ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM z) (n+radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0,1) Z)
    (hd : spectralValueDet
      (spectralPhysicalValueMap (spectralPhysicalPair
        (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Y lam) R))
      (spectralPhysicalValueMap (spectralPhysicalPair
        (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Z lam) R)) ≠ 0) :
    HasDerivAt (radialMatchedCanonicalRobin n z R Y Z)
      (deriv (radialMatchedCanonicalRobin n z R Y Z) lam) lam ∧
    (deriv u.first R,deriv u.second R)=radialMatchedCanonicalRobin n z R Y Z lam
      (u.first R,u.second R) := by
  have hR₁ : 1 ≤ R := by linarith [innerBoundaryRadius_bounds.1]
  have hM := (radialMatchedCanonicalRobin_analyticAt n ell z R hR₁ Y Z hY hZ lam hd).differentiableAt.hasDerivAt
  have hb₀ := homogeneous_matched_pair_canonical_robin n z hX hz ((ell : ℂ)*(ell+10)) N hN lam hhalf
    u.first u.second u.first_c2 u.second_c2 u.equation u.bounded u.first_top u.second_top Y Z
    (by simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hY)
    (by simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hZ) R hR hd
  exact ⟨hM,hb₀⟩

end DefocusingNLS

end OAI
