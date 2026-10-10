import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteMatchedSymbol

namespace OAI

/-! The actual matched eigenpair has the required outgoing logarithmic
symbol, with the two canonical columns constructed internally. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem spectralRemote_matched_state_symbol
    (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (eta : ℂ) (N : ℕ) (hN : 7 ≤ N)
    (lam : ℂ) (hhalf : -(1/32 : ℝ) ≤ lam.re)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) eta lam f g)
    (hbounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(f r,g r)‖ ≤ M)
    (hL2f : IntegrableOn (fun r => r^11*‖iteratedDeriv N f r‖^2) (Ioi 0))
    (hL2g : IntegrableOn (fun r => r^11*‖iteratedDeriv N g r‖^2) (Ioi 0)) :
    HasLogJetBound 1 (spectralRemoteEigenpairState f g) := by
  let m := n+radialInnerShootingThreshold
  let nu := radialShootingNu m z
  have hm : 1 ≤ m := radialShootingInner_power_pos n (profileMatchingParameter z)
  obtain ⟨Yp,hYp⟩ := canonical_holomorphic_circular_allOrders nu nu (star nu) eta
    (radialShootingM z) m hm (Real.log innerBoundaryRadius) hX (radialShootingM_ne_zero z) (1,0)
  obtain ⟨Ym,hYm⟩ := canonical_holomorphic_circular_allOrders nu nu (star nu) eta
    (radialShootingM z) m hm (Real.log innerBoundaryRadius) hX (radialShootingM_ne_zero z) (0,1)
  exact spectralRemote_matched_eigenpair_symbol n z hX hz eta N hN lam hhalf f g hf hg he
    hbounded hL2f hL2g Yp Ym hYp hYm

end DefocusingNLS

end OAI
