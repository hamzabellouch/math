import OAI.GroupTheory.PolycyclicRecognition.Analysis.CocycleCompactWords
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordLifts
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricChainWords

namespace OAI

/-! # Pulling compact-word sublinearity to a proper chain metric -/

noncomputable section
namespace PolycyclicRecognition

open Metric Set

variable {G H E : Type*} [Group G] [Group H] [TopologicalSpace G]
  [MetricSpace H] [IsIsometricSMul H H] [ProperSpace H] [NormedAddCommGroup E]

/-- A continuous homomorphism maps a compact generating ball to a compact
set. Its pulled-back cocycle inherits the metric sublinearity estimate. -/
theorem sublinear_comp_of_compact_word_estimates
    (f : H →* G) (hf : Continuous f) (b : G → E) (C : LinearMetricChains H)
    (hsub : ∀ K : Set G, IsCompact K →
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ (u : ℕ → G) (m : ℕ),
        (∀ i < m, u i ∈ K) → ‖b (wordPrefix u m)‖ ≤ ε * (m : ℝ) + B) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ h, ‖b (f h)‖ ≤ ε * dist 1 h + B := by
  let K : Set H := closedBall 1 C.step
  have hK : IsCompact K := isCompact_closedBall 1 C.step
  have hs : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ (u : ℕ → H) (m : ℕ),
      (∀ i < m, u i ∈ K) → ‖(b ∘ f) (wordPrefix u m)‖ ≤ ε * (m : ℝ) + B := by
    intro ε hε
    obtain ⟨B, hB, hb⟩ := hsub (f '' K) (hK.image hf) ε hε
    refine ⟨B, hB, fun u m hu => ?_⟩
    simpa only [Function.comp_apply, map_wordPrefix] using
      hb (fun i => f (u i)) m (fun i hi => ⟨u i, hu i hi, rfl⟩)
  apply sublinear_of_compact_word_estimates (b ∘ f) K hs (fun h => dist 1 h)
    (fun _ => dist_nonneg) (a := C.slope + C.error) (add_nonneg C.slope_nonneg C.error_nonneg)
  intro h
  obtain ⟨l, hl, he, hn⟩ := C.wordFactorization h
  refine ⟨l, hl, he, hn.trans ?_⟩
  nlinarith [C.slope_nonneg, C.error_nonneg,
    mul_nonneg C.error_nonneg (dist_nonneg (x := (1 : H)) (y := h))]

end PolycyclicRecognition

end

end OAI
