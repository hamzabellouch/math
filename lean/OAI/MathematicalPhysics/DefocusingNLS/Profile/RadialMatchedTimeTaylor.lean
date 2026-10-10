import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FixedCutoffProfileTaylor
import OAI.MathematicalPhysics.DefocusingNLS.Profile.CartesianTransportSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffSymbolSampling
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedProfileBounds

namespace OAI

/-! # The actual matched profile has a uniform logarithmic-time Taylor bound -/

open Set
open scoped SchwartzMap ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem radialMatched_fixedProfile_time_taylor (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (k : ℝ) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0) :
    let a := radialShootingA n
    let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
    let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
    let Q := radialMatchedCartesian n z
    let hQ := radialMatchedCartesian_contDiff n z hX hz
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : Radius), 2 ≤ L.1 → ∀ t : ℝ, |t| ≤ 2 * Real.log 2 →
      ‖fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ (expandingRadius L.1 t) -
        fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1 -
        t • fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianTransport Q)
          (cartesianTransport_contDiff Q hQ) L.1‖ ≤ C * |t| ^ 2 := by
  intro a ha ha1 Q hQ
  have hs := radialMatchedCartesian_global_symbol n z hX hz
  have hT := cartesianTransport_global_symbol a Q hQ hs
  have hTT := cartesianTransport_global_symbol a (cartesianTransport Q)
    (cartesianTransport_contDiff Q hQ) hT
  obtain ⟨B, hB, hb⟩ := cutoffProfile_sampling_of_global_symbol a k ha ha1 hk χ hχ hχzero
    (cartesianTransport (cartesianTransport Q))
    (cartesianTransport_contDiff _ (cartesianTransport_contDiff Q hQ)) hTT
  refine ⟨(2 ^ a + 2 ^ (k - 6)) * B, by positivity, ?_⟩
  intro L hL t ht
  exact fixedCutoffProfile_logRadius_taylor a k ha ha1 hk L hL χ hχ Q hQ B hB
    (fun R => hb R.1 R.2) t ht

end DefocusingNLS

end OAI
