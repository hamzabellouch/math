import OAI.Analysis.KadisonKastler.ConjugationAveragedState

namespace OAI

/-! # Invariant extensions preserving prescribed state values

The abelian action is averaged as a discrete group. No continuity or
normality of the initial ambient state is needed.
-/

namespace KadisonKastler

open NaimarkZFC

noncomputable section

variable {G H : Type*} [CommGroup G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_invariant_state_preserving_values
    (U : G →* unitary (H →L[ℂ] H))
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ)
    (A : Set (H →L[ℂ] H))
    (hA : ∀ T ∈ A, ∀ g : G, φ (unitaryConj (U g) T)=φ T) :
    ∃ ψ : (H →L[ℂ] H) →L[ℂ] ℂ, IsState ψ ∧
      (∀ (g : G) (T : H →L[ℂ] H), ψ (unitaryConj (U g) T)=ψ T) ∧
      ∀ T ∈ A, ψ T=φ T := by
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  let m := abelianScalarInvariantMean G
  exact ⟨m.averagedState U φ,m.averagedState_isState U φ hφ,
    m.averagedState_invariant U φ,
    fun T hT => m.averagedState_eq_of_invariant_values U φ T (hA T hT)⟩

end

end KadisonKastler

end OAI
