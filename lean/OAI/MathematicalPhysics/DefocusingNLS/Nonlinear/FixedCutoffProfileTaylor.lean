import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FixedCutoffProfileBound
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.NormedCurveTaylor

namespace OAI

/-! # Uniform logarithmic-radius Taylor expansion of the actual cutoff profile -/

open Set
open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

private theorem logarithmicRadius_nearby (L t : ℝ) (hL : 2 ≤ L)
    (ht : |t| ≤ 2 * Real.log 2) :
    1 ≤ expandingRadius L t ∧ L ≤ 2 * expandingRadius L t ∧
      expandingRadius L t ≤ 2 * L := by
  have hlo : (1 / 2 : ℝ) ≤ Real.exp (t / 2) := by
    have h := Real.exp_le_exp.mpr (show -Real.log 2 ≤ t / 2 by linarith [(abs_le.mp ht).1])
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div] using h
  have hhi : Real.exp (t / 2) ≤ 2 := by
    have h := Real.exp_le_exp.mpr (show t / 2 ≤ Real.log 2 by linarith [(abs_le.mp ht).2])
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  dsimp only [expandingRadius]
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem fixedCutoffProfile_logRadius_taylor (a k : ℝ) (ha : 0 < a)
    (ha1 : a < 1) (hk : 8 < k) (L : Radius) (hL : 2 ≤ L.1)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ R : Radius, ‖schwartzTorusSample a k R.1 ha1 hk R.2
      (radianFourierKernel (cutoffProfileSchwartz R.1
        (lt_of_lt_of_le zero_lt_one R.2) χ hχ
        (cartesianTransport (cartesianTransport Q))
        (cartesianTransport_contDiff _ (cartesianTransport_contDiff Q hQ))))‖ ≤ B)
    (t : ℝ) (ht : |t| ≤ 2 * Real.log 2) :
    ‖fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ (expandingRadius L.1 t) -
      fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1 -
      t • fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianTransport Q)
        (cartesianTransport_contDiff Q hQ) L.1‖ ≤
      ((2 ^ a + 2 ^ (k - 6)) * B) * |t| ^ 2 := by
  let Q₁ := cartesianTransport Q
  let hQ₁ := cartesianTransport_contDiff Q hQ
  let Q₂ := cartesianTransport Q₁
  let hQ₂ := cartesianTransport_contDiff Q₁ hQ₁
  let u := fun s => fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ (expandingRadius L.1 s)
  let v := fun s => fixedCutoffProfile a k ha ha1 hk L χ hχ Q₁ hQ₁ (expandingRadius L.1 s)
  let w := fun s => fixedCutoffProfile a k ha ha1 hk L χ hχ Q₂ hQ₂ (expandingRadius L.1 s)
  have h := normedCurve_firstOrder_bound u v w (2 * Real.log 2)
    ((2 ^ a + 2 ^ (k - 6)) * B) (by positivity)
    (fun s _ => hasDerivAt_fixedCutoffProfile_logRadius a k ha ha1 hk L χ hχ Q hQ L.1 s (by linarith))
    (fun s _ => hasDerivAt_fixedCutoffProfile_logRadius a k ha ha1 hk L χ hχ Q₁ hQ₁ L.1 s (by linarith))
    (fun s hs => by
      obtain ⟨hR, hLR, hRL⟩ := logarithmicRadius_nearby L.1 s hL (abs_le.mpr hs)
      exact fixedCutoffProfile_norm_le a k ha ha1 hk L ⟨expandingRadius L.1 s, hR⟩
        hLR hRL χ hχ Q₂ hQ₂ B (hb _)) t ht
  simpa only [u, v, expandingRadius, zero_div, Real.exp_zero, mul_one] using h

end DefocusingNLS

end OAI
