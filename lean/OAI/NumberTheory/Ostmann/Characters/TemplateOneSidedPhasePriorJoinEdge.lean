import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingAction

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open DiagonalEstimate HigherBiasSource HigherBiasSource.SourceTemplate TemplateDiagonalMatching
attribute [local instance] Classical.propDecidable

theorem changed_actualCode_sourceEdge {k : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (hj : j<k) (σ ρ : Equiv.Perm (ActualCopied cfg m j))
    (hσ : ∀i,IsCopiedBulk cfg m j (σ i) ↔ IsCopiedBulk cfg m j i)
    (hρ : ∀i,IsCopiedBulk cfg m j (ρ i) ↔ IsCopiedBulk cfg m j i)
    (hcode : ¬∀i,actualCopiedCode cfg m j (σ i)=actualCopiedCode cfg m j (ρ i)) :
    ∃L S : SurvivingPrimeIndex k j (sourceWidth cfg m), ∃positive : Bool,
      L≠S ∧
      survivingDifferenceGraph k j hj (sourceWidth cfg m)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ) S L=(if positive then 2 else -2) ∧
      survivingDifferenceGraph k j hj (sourceWidth cfg m)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ) L S=0 ∧
      ∃z : Word k j × Fin m, ∃a₀ : Fin j, ∃b : Bool,
        (L=.inl (copiedBulk cfg m j z) ∧ S=.inr (copiedRetiredOutside cfg m j hj.le false a₀ b)) ∨
        (L=.inr (copiedRetiredOutside cfg m j hj.le true a₀ b) ∧ S=.inl (copiedBulk cfg m j z)) := by
  obtain ⟨z,hz⟩ := exists_bulk_code_change cfg m j σ ρ hσ hρ hcode
  obtain ⟨a₀,b,hLS,hLB,h | h⟩ := copied_changed_code_surviving_edge cfg m j hj σ ρ
    (fun i hi=>(hσ i).mpr hi) (fun i hi=>(hρ i).mpr hi) z hz
  · obtain ⟨hforward,hrev⟩ := h
    rcases hforward with hforward | hforward
    · exact ⟨_,_,true,hLS,hforward,hrev,z,a₀,b,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨_,_,false,hLS,hforward,hrev,z,a₀,b,Or.inl ⟨rfl,rfl⟩⟩
  · obtain ⟨hforward,hrev⟩ := h
    rcases hforward with hforward | hforward
    · exact ⟨_,_,true,hLB.symm,hforward,hrev,z,a₀,b,Or.inr ⟨rfl,rfl⟩⟩
    · exact ⟨_,_,false,hLB.symm,hforward,hrev,z,a₀,b,Or.inr ⟨rfl,rfl⟩⟩

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
