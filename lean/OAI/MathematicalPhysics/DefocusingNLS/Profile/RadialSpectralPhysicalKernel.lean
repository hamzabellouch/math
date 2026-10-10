import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPhysicalPencil
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HarmonicRadialNonvanishing
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralMode

namespace OAI

/-! A radial mode with an outgoing boundary condition gives a nonzero compact kernel. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialSpectralMode_physical_kernel (n ell i N : ℕ) (_hN : 7 ≤ N)
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
    (M : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hb : (deriv u.first R,deriv u.second R)=M (u.first R,u.second R)) :
    let hR₀ : 0 < R := (by linarith [innerBoundaryRadius_bounds.1])
    ∃ v : SpectralRadialObservationSpace R, v ≠ 0 ∧
      F.compactPencil ell hR₀ i
        (radialMatchedWeakOperator n ell z hX hz R hR₀ lam
          (spectralFluxBoundary R (radialMatchedMassFunction n z R)
            (radialMatchedTransportFunction n z R)
            (spectralGaugeRobin (radialMatchedProfile n z R)
              (deriv (radialMatchedProfile n z) R) M))) v=v := by
  dsimp only
  have hR₀ : 0 < R := by linarith [innerBoundaryRadius_bounds.1]
  have hη : (((ell : ℝ)*(ell+10) : ℝ) : ℂ)=(ell : ℂ)*(ell+10) := by push_cast; rfl
  have he : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam u.first u.second := by
    rw [hη]
    exact u.equation
  have hne := harmonicRadialEigenpair_nonzero_on_ball _ _ _ _ u.first u.second _ _
    (radialMatchedProfile_differentiable n z hX hz).continuous.continuousOn
    u.first_c2 u.second_c2 u.equation u.nonzero R hR₀
  exact radialMatchedPhysical_pencil n ell i z hX hz R l hR₀ F hw hp ha lam
    u.first u.second u.first_c2 u.second_c2 he hne M hb

end DefocusingNLS

end OAI
