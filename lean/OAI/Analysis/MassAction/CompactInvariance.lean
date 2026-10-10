import OAI.Analysis.MassAction.CompactBounds
import OAI.Analysis.MassAction.MassActionRegularity
import OAI.Analysis.MassAction.CompactContinuation

namespace OAI

noncomputable section

namespace Problem326

/-- The quantitative global conclusion only needs a compact positive
forward-invariant set, not its polyhedral or convex structure. -/
theorem global_bounds_of_compact_invariant {d : ℕ}
    (N : ReactionNetwork d) (κ : Reaction N → ℝ) (x0 : Fin d → ℝ)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (hx0 : x0 ∈ K)
    (hpos : K ⊆ {x | PositiveState x}) (hinv : IsForwardInvariant N κ K) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      (∃ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x) ∧
      ∀ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x →
        ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, ε ≤ x t i ∧ x t i ≤ ε⁻¹ := by
  obtain ⟨ε, hε, hεone, hbound⟩ := compact_positive_uniform_bounds hK
    (fun x hx => hpos hx)
  refine ⟨ε, hε, hεone, (hinv x0 hx0).1, ?_⟩
  intro x hx t ht i
  have hfinite : IsForwardSolutionOn N κ x0 t x := by
    refine ⟨hx.1, ?_, ?_⟩
    · intro s hs
      exact (hx.2 s hs.1).continuousAt.continuousWithinAt
    · intro s hs
      exact hx.2 s hs.1.le
  have hmem := ((hinv x0 hx0).2 t x ht hfinite).1 t ⟨ht, le_rfl⟩
  exact hbound (x t) hmem i

end Problem326

end

end OAI
