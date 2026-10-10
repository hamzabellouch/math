import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralCanonicalKernel
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralCanonicalBoundaryData
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralCanonicalSourceLift

namespace OAI

/-! A generalized radial mode with its canonical outgoing condition yields a nonzero analytic chain. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable local instance canonicalSourceChainNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialSpectralMode_canonical_source_chain (n ell i N : ℕ) (hN : 7 ≤ N)
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
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam) (Z lam) R)) ≠ 0)
    (v w : ℝ → ℂ) (hv : ContDiff ℝ 2 v) (hw₂ : ContDiff ℝ 2 w)
    (he : IsHarmonicRadialSourcePair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam v w u.first u.second)
    (hb : (deriv v R,deriv w R)=
      radialMatchedCanonicalRobin n z R Y Z lam (v R,w R)+
      deriv (radialMatchedCanonicalRobin n z R Y Z) lam (u.first R,u.second R)) :
    let hR₀ : 0 < R := (by linarith [innerBoundaryRadius_bounds.1])
    let P := fun t => F.compactPencil ell hR₀ i
      (radialMatchedWeakOperator n ell z hX hz R hR₀ t (radialMatchedCanonicalFlux n z R Y Z t))
    ∃ v₀ v₁ : SpectralRadialObservationSpace R, v₀ ≠ 0 ∧ P lam v₀=v₀ ∧
      v₁-P lam v₁=deriv P lam v₀ := by
  intro hR₀ P
  obtain ⟨hM,hb₀⟩ := radialSpectralMode_canonical_boundary_data n ell N hN z hX hz
    R hR lam hhalf u Y Z hY hZ hd
  have hresult := radialSpectralMode_canonical_source_lift n ell i N hN z hX hz R l hR F hw hp ha
    lam hhalf u Y Z hM hb₀ v w hv hw₂ he hb
  exact hresult

end DefocusingNLS

end OAI
