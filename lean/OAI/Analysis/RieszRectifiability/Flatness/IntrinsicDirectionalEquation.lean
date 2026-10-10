import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.PlaneTestExtensions
import OAI.Analysis.RieszRectifiability.Flatness.PlanePairingPullback

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set SchwartzMap
open scoped NNReal ContDiff

theorem intrinsic_directional_equation_of_ambient {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ)
    (hambient : ∀ (φ : Ambient d → ℝ) (J B : ℝ≥0),
      HasCompactSupport φ → LipschitzWith J φ → (∀ x, |φ x| ≤ (B : ℝ)) →
      Integrable φ (coordinatePlaneMeasure (affinePlaneSection a L)) →
      (∫ x, φ x ∂coordinatePlaneMeasure (affinePlaneSection a L)) = 0 →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        heightPairingOn n (coordinatePlaneMeasure (affinePlaneSection a L)) a (ball a R) f φ = 0)
    (g : Ambient n → ℝ) (hc : HasCompactSupport g) (hg : ContDiff ℝ ∞ g) (v : Ambient n) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      heightPairingOn n volume (0 : Ambient n) (ball 0 R)
        (fun u => f (a + L u)) (fun u => fderiv ℝ g u v) = 0 := by
  obtain ⟨φ, J, B, hcφ, hφ, hB, hext, hI, hzero⟩ :=
    exists_compact_ambient_directional_test a L g hc hg v
  obtain ⟨R₀, hR₀, hR⟩ := hambient φ J B hcφ hφ hB hI hzero
  refine ⟨R₀, hR₀, fun R hRR => ?_⟩
  have h := hR R hRR
  rw [heightPairingOn_affine_pullback] at h
  have heq : (fun u => φ (a + L u)) = fun u => fderiv ℝ g u v := funext hext
  rwa [heq] at h

end

end RieszRectifiability

end OAI
