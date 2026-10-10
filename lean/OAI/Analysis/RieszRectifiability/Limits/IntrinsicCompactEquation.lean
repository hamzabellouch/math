import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.IntrinsicDirectionalEquation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set SchwartzMap
open scoped NNReal

theorem intrinsic_compact_schwartz_equation_of_ambient {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ)
    (hambient : ∀ (φ : Ambient d → ℝ) (J B : ℝ≥0),
      HasCompactSupport φ → LipschitzWith J φ → (∀ x, |φ x| ≤ (B : ℝ)) →
      Integrable φ (coordinatePlaneMeasure (affinePlaneSection a L)) →
      (∫ x, φ x ∂coordinatePlaneMeasure (affinePlaneSection a L)) = 0 →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        heightPairingOn n (coordinatePlaneMeasure (affinePlaneSection a L)) a (ball a R) f φ = 0)
    (g : 𝓢(Ambient n, ℝ)) (hc : HasCompactSupport g) (hg : (∫ x, g x) = 0) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      heightPairingOn n volume (0 : Ambient n) (ball 0 R) (fun u => f (a + L u)) g = 0 := by
  obtain ⟨K, B, hK, hB⟩ := schwartz_real_bounded_lipschitz g
  obtain ⟨φ, J, hcφ, hφ, hBφ, hext, hI, hmean⟩ :=
    exists_compact_ambient_plane_test a L g hc K B hK hB
  obtain ⟨R₀, hR₀, hR⟩ := hambient φ J B hcφ hφ hBφ hI (hmean.trans hg)
  refine ⟨R₀, hR₀, fun R hRR => ?_⟩
  have h := hR R hRR
  rw [heightPairingOn_affine_pullback] at h
  have heq : (fun u => φ (a + L u)) = g := funext hext
  rwa [heq] at h

end

end RieszRectifiability

end OAI
