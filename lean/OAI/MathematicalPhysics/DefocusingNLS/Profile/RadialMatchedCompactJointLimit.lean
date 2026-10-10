import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPencilJointLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilJointLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFluxSmoothness

namespace OAI

/-! Joint norm convergence for the actual observed compact pencil. -/

open Filter Topology
namespace DefocusingNLS
open ProfileCertificate

noncomputable local instance compactJointNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedPencil_joint_tendsto (ell : ℕ) (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0) (R : ℝ) (hLR : radialShootingR (profileMatchingParameter z₀)<R)
    (F : SpectralPenaltyFamily R (radialShootingR (profileMatchingParameter z₀)))
    (ζ₀ : ℂ) (B : ℕ → ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (B₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : Tendsto (fun p : ℕ × ℂ => B p.1 p.2) (atTop ×ˢ 𝓝 ζ₀) (𝓝 B₀)) :
    let hL := radialMatchedCore_radius_pos z₀
    let hR := hL.trans hLR
    Tendsto (fun p : ℕ × ℂ => F.compactPencil ell hR p.1
      (radialMatchedWeakOperator (s p.1) ell (z p.1) (hX p.1) (hm p.1)
        R hR p.2 (B p.1 p.2))) (atTop ×ˢ 𝓝 ζ₀)
      (𝓝 (F.limitPencil ell hL hLR (radialMatchedLimitWeakOperator ell z₀
        (radialMatchedFreeMassFunction_continuous s hs z z₀ hz hX hm) R hR ζ₀ B₀))) := by
  let hL := radialMatchedCore_radius_pos z₀
  let hR := hL.trans hLR
  have hK := radialMatchedWeakOperator_joint_tendsto ell s hs z z₀ hz hX hm R hR ζ₀ B B₀ hB
  exact F.compactPencil_joint_tendsto ell hL hLR ζ₀ _ _ hK

end DefocusingNLS

end OAI
