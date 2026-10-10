import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedTailSelection
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingTail

namespace OAI

/-! Tail energy selects the outgoing plane at every earlier matching radius. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "V" => ℂ × ℂ
local notation "V₄" => V × V

theorem radialMatched_state_canonical_tail_span_at
    (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (eta : ℂ) (N : ℕ) (hN : 7 ≤ N)
    (lam : ℂ) (hhalf : -(1 / 32 : ℝ) ≤ lam.re)
    (Z : ℝ → V₄) (R T : ℝ) (hR : innerBoundaryRadius<R) (hRT : R≤T)
    (hZeq : ∀ r, R≤r → HasDerivAt Z
      (spectralPhysicalCircularField
        (radialShootingNu (n+radialInnerShootingThreshold) z-2*lam)
        (star (radialShootingNu (n+radialInnerShootingThreshold) z)-2*lam)
        eta (n+radialInnerShootingThreshold) (radialMatchedProfile n z r) r (Z r)) r)
    (hUs : ContDiffOn ℝ ∞ (fun r => spectralPhysicalValueMap (Z r)) (Ioi T))
    (hbounded : ∃ M : ℝ, 0≤M ∧ ∀ r, T≤r → ‖spectralPhysicalValueMap (Z r)‖≤M)
    (hL2p : IntegrableOn (fun r => r^11*
      ‖(iteratedDeriv N (fun s => spectralPhysicalValueMap (Z s)) r).1‖^2) (Ioi T))
    (hL2m : IntegrableOn (fun r => r^11*
      ‖(iteratedDeriv N (fun s => spectralPhysicalValueMap (Z s)) r).2‖^2) (Ioi T))
    (Yp Ym : ℂ → ℝ → V₄)
    (hYp : IsCanonicalHolomorphicColumn (radialShootingNu (n + radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n + radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1, 0) Yp)
    (hYm : IsCanonicalHolomorphicColumn (radialShootingNu (n + radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n + radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0, 1) Ym)
    :
    ∃ a : V, Z R =
      a.1 • spectralPhysicalPair (radialShootingNu (n + radialInnerShootingThreshold) z - 2 * lam)
        (star (radialShootingNu (n + radialInnerShootingThreshold) z) - 2 * lam) (Yp lam) R +
      a.2 • spectralPhysicalPair (radialShootingNu (n + radialInnerShootingThreshold) z - 2 * lam)
        (star (radialShootingNu (n + radialInnerShootingThreshold) z) - 2 * lam) (Ym lam) R := by
  let ν := radialShootingNu (n+radialInnerShootingThreshold) z
  let Zp := spectralPhysicalPair (ν-2*lam) (star ν-2*lam) (Yp lam)
  let Zm := spectralPhysicalPair (ν-2*lam) (star ν-2*lam) (Ym lam)
  obtain ⟨c,hc⟩ := radialMatched_state_canonical_tail_span n z hX hz eta N hN lam hhalf
    Z T (lt_of_lt_of_le hR hRT) (fun r hr => hZeq r (hRT.trans hr)) hUs hbounded
    hL2p hL2m Yp Ym hYp hYm T le_rfl
  refine ⟨c,?_⟩
  have hR₀ : 0<R := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hR
  exact homogeneousPhysicalOutgoingPlane_backward (ν-2*lam) (star ν-2*lam) eta
    (n+radialInnerShootingThreshold) (radialMatchedProfile n z) Z Zp Zm R T hR₀ hRT
    ((radialMatchedProfile_contDiffOn n z hX hz).continuousOn.mono
      (fun _ hr => hR₀.trans_le hr.1))
    (fun r hr => hZeq r hr.1)
    (fun r hr => homogeneous_matched_canonicalColumn_derivative n z eta lam (1,0)
      Yp hYp r (hR.trans_le hr.1))
    (fun r hr => homogeneous_matched_canonicalColumn_derivative n z eta lam (0,1)
      Ym hYm r (hR.trans_le hr.1)) c hc

end DefocusingNLS

end OAI
