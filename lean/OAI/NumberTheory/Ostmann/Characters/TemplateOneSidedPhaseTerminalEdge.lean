import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalIndexedSource

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale HigherBiasSourceWord ParityActions
attribute [local instance] Classical.propDecidable

theorem sourceTerminal_changed_edge
    {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ) (hn : n+1≤k)
    {σ τ : Reassignments k n (wordSize k ℓ)} (hστ : σ≠τ) :
    ∃ z : BulkSlot k n (wordSize k ℓ), ∃j : Fin (n+1), ∃b positive : Bool,
      let hm : wordSize k ℓ ≤ sourceWidth w.configuration (wordSize k ℓ) .word := by
        rw [sourceWidth_word];omega
      let hw : ∀j : Fin (n+1),0<sourceWidth w.configuration (wordSize k ℓ) (.anchor j false) := by
        intro j;rw [sourceWidth_anchor];omega
      let L := prefixBulkEmbedding k n (sourceWidth w.configuration (wordSize k ℓ)) (wordSize k ℓ) hm z
      let S := smallAnchorConstituent k n hn (sourceWidth w.configuration (wordSize k ℓ)) hw j b
      L≠S ∧ sourceTerminalGraph w n σ τ S L=(if positive then 2 else -2) ∧
        sourceTerminalGraph w n σ τ L S=0 := by
  have hm : wordSize k ℓ ≤ sourceWidth w.configuration (wordSize k ℓ) .word := by
    rw [sourceWidth_word];omega
  have hw : ∀j : Fin (n+1),0<sourceWidth w.configuration (wordSize k ℓ) (.anchor j false) := by
    intro j;rw [sourceWidth_anchor];omega
  obtain ⟨z,j,b,hLS,hf,hr⟩ := prefix_distinct_reassignments_edge k n hn
    (sourceWidth w.configuration (wordSize k ℓ)) hw (wordSize k ℓ) hm (Ne.symm hστ)
  rcases hf with hf|hf
  · exact ⟨z,j,b,true,hLS,hf,hr⟩
  · exact ⟨z,j,b,false,hLS,hf,hr⟩

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
