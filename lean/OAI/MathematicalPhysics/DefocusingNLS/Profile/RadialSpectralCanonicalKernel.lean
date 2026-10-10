import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralPhysicalKernel
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalFluxLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedOutgoing
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HarmonicRadialNonvanishing
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralMode

namespace OAI

/-! Actual radial eigenmodes give nonzero kernels of the canonical compact pencil. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialSpectralMode_canonical_kernel (n ell i N : ℕ) (hN : 7 ≤ N)
    (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R l : ℝ) (hR : innerBoundaryRadius < R)
    (F : SpectralPenaltyFamily R l)
    (hw : (F.weight i).density=radialMatchedMassFunction n z)
    (hp : F.pressure i=fun r => ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)))
    (ha : F.scale i=radialShootingA n) (lam : ℂ) (hhalf : -(1/32 : ℝ) ≤ lam.re)
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
    let hR₀ : 0 < R := (by linarith [innerBoundaryRadius_bounds.1])
    ∃ v : SpectralRadialObservationSpace R, v ≠ 0 ∧
      F.compactPencil ell hR₀ i
        (radialMatchedWeakOperator n ell z hX hz R hR₀ lam (radialMatchedCanonicalFlux n z R Y Z lam)) v=v := by
  dsimp only
  unfold radialMatchedCanonicalFlux radialMatchedFluxBoundary
  have hb := homogeneous_matched_pair_canonical_robin n z hX hz ((ell : ℂ)*(ell+10)) N hN lam hhalf
    u.first u.second u.first_c2 u.second_c2 u.equation u.bounded u.first_top u.second_top Y Z
    (by simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hY)
    (by simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using hZ) R hR hd
  exact radialSpectralMode_physical_kernel n ell i N hN z hX hz R l hR F hw hp ha lam hhalf u _ hb

end DefocusingNLS

end OAI
