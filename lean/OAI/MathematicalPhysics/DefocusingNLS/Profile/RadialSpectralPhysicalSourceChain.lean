import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralPhysicalKernel
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPhysicalSourcePencil

namespace OAI

/-! The regular radial mode supplies a nonzero leading vector for the physical chain lift. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

noncomputable local instance physicalModeSourceChainNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialSpectralMode_physical_source_chain (n ell i N : ℕ) (_hN : 7 ≤ N)
    (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R l : ℝ) (hR : innerBoundaryRadius < R)
    (F : SpectralPenaltyFamily R l)
    (hw : (F.weight i).density=radialMatchedMassFunction n z)
    (hp : F.pressure i=fun r => ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)))
    (ha : F.scale i=radialShootingA n) (lam : ℂ) (_hhalf : -(1/32 : ℝ) ≤ lam.re)
    (u : RadialSpectralMode (radialShootingA n) (radialShootingB (profileMatchingParameter z))
      (n+radialInnerShootingThreshold) N (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam)
    (v w : ℝ → ℂ) (hv : ContDiff ℝ 2 v) (hw₂ : ContDiff ℝ 2 w)
    (he : IsHarmonicRadialSourcePair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) ((ell : ℂ)*(ell+10)) lam v w u.first u.second)
    (M : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (M' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hM : HasDerivAt M M' lam)
    (hb₀ : (deriv u.first R,deriv u.second R)=M lam (u.first R,u.second R))
    (hb : (deriv v R,deriv w R)=M lam (v R,w R)+M' (u.first R,u.second R)) :
    let hR₀ : 0 < R := (by linarith [innerBoundaryRadius_bounds.1])
    let B := fun t => spectralFluxBoundary R (radialMatchedMassFunction n z R)
      (radialMatchedTransportFunction n z R)
      (spectralGaugeRobin (radialMatchedProfile n z R) (deriv (radialMatchedProfile n z) R) (M t))
    let P := fun t => F.compactPencil ell hR₀ i (radialMatchedWeakOperator n ell z hX hz R hR₀ t (B t))
    ∃ v₀ v₁ : SpectralRadialObservationSpace R, v₀ ≠ 0 ∧ P lam v₀=v₀ ∧
      v₁-P lam v₁=deriv P lam v₀ := by
  intro hR₀ B P
  have hη : (((ell : ℝ)*(ell+10) : ℝ) : ℂ)=(ell : ℂ)*(ell+10) := by push_cast; rfl
  have he₀ : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam u.first u.second := by
    rw [hη]
    exact u.equation
  have he₁ : IsHarmonicRadialSourcePair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam v w u.first u.second := by
    rw [hη]
    exact he
  have hne := harmonicRadialEigenpair_nonzero_on_ball _ _ _ _ u.first u.second _ _
    (radialMatchedProfile_differentiable n z hX hz).continuous.continuousOn
    u.first_c2 u.second_c2 u.equation u.nonzero R hR₀
  have hresult := radialMatchedPhysical_source_pencil n ell i z hX hz R l hR₀ F hw hp ha lam
    v w u.first u.second hv hw₂ u.first_c2 u.second_c2 he₀ he₁ hne
    M M' hM hb₀ hb
  exact hresult

end DefocusingNLS

end OAI
