import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingAction
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingVariables

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open DiagonalEstimate HigherBiasSource HigherBiasSource.SourceTemplate TemplateDiagonalMatching
attribute [local instance] Classical.propDecidable

theorem copied_matching_surviving_squarePhase {k : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (hj : j<k) (σ ρ : Equiv.Perm (ActualCopied cfg m j))
    (hσ : CopiedBulkPreserving cfg m j σ) (hρ : CopiedBulkPreserving cfg m j ρ)
    (z : Word k j × Fin m)
    (hcode : bulkCode k j m (copiedBulkImage cfg m j σ hσ z) ≠
      bulkCode k j m (copiedBulkImage cfg m j ρ hρ z))
    (p : SurvivingPrimeIndex k j (sourceWidth cfg m) → ℕ) [∀i,Fact (p i).Prime]
    (hc : Pairwise (fun i h=>(p i).Coprime (p h)))
    (χ : SurvivingPrimeIndex k j (sourceWidth cfg m) → (q:ℕ) → MulChar (ZMod q) ℂ)
    (hχ : ∀i,2<orderOf (χ i (p i)))
    (a : SurvivingPrimeIndex k j (sourceWidth cfg m) → (q:ℕ) → ZMod q)
    (ζ : SurvivingPrimeIndex k j (sourceWidth cfg m) → ℕ → ℂ)
    (hζ : ∀i q,‖ζ i q‖≤1) (P : ℕ) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (ht : ∀i,HistoryFrequencyUnits (p i) j s t)
    (hu : ∀i,HistoryFrequencyUnits (p i) j s u) :
    ∃a₀ : Fin j, ∃b : Bool,
      SurvivingSquarePhase k j hj (sourceWidth cfg m)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ) p χ a ζ P s t u
        (.inl (copiedBulk cfg m j z)) (.inr (copiedRetiredOutside cfg m j hj.le false a₀ b)) ∨
      SurvivingSquarePhase k j hj (sourceWidth cfg m)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ) p χ a ζ P s t u
        (.inr (copiedRetiredOutside cfg m j hj.le true a₀ b)) (.inl (copiedBulk cfg m j z)) := by
  obtain ⟨a₀,b,hLS,hLB,h | h⟩ := copied_changed_code_surviving_edge cfg m j hj σ ρ hσ hρ z hcode
  · refine ⟨a₀,b,Or.inl ?_⟩
    exact survivingPhasePair_square k j hj (sourceWidth cfg m) _ _ p hc χ hχ a ζ hζ P s t u ht hu
      _ _ hLS h.1 h.2
  · refine ⟨a₀,b,Or.inr ?_⟩
    exact survivingPhasePair_square k j hj (sourceWidth cfg m) _ _ p hc χ hχ a ζ hζ P s t u ht hu
      _ _ hLB.symm h.1 h.2

theorem changed_actualCode_surviving_squarePhase {k : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (hj : j<k) (σ ρ : Equiv.Perm (ActualCopied cfg m j))
    (hσ : ∀i,IsCopiedBulk cfg m j (σ i) ↔ IsCopiedBulk cfg m j i)
    (hρ : ∀i,IsCopiedBulk cfg m j (ρ i) ↔ IsCopiedBulk cfg m j i)
    (hcode : ¬∀i,actualCopiedCode cfg m j (σ i)=actualCopiedCode cfg m j (ρ i))
    (p : SurvivingPrimeIndex k j (sourceWidth cfg m) → ℕ) [∀i,Fact (p i).Prime]
    (hc : Pairwise (fun i h=>(p i).Coprime (p h)))
    (χ : SurvivingPrimeIndex k j (sourceWidth cfg m) → (q:ℕ) → MulChar (ZMod q) ℂ)
    (hχ : ∀i,2<orderOf (χ i (p i)))
    (a : SurvivingPrimeIndex k j (sourceWidth cfg m) → (q:ℕ) → ZMod q)
    (ζ : SurvivingPrimeIndex k j (sourceWidth cfg m) → ℕ → ℂ)
    (hζ : ∀i q,‖ζ i q‖≤1) (P : ℕ) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (ht : ∀i,HistoryFrequencyUnits (p i) j s t)
    (hu : ∀i,HistoryFrequencyUnits (p i) j s u) :
    ∃z : Word k j × Fin m, ∃a₀ : Fin j, ∃b : Bool,
      SurvivingSquarePhase k j hj (sourceWidth cfg m)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ) p χ a ζ P s t u
        (.inl (copiedBulk cfg m j z)) (.inr (copiedRetiredOutside cfg m j hj.le false a₀ b)) ∨
      SurvivingSquarePhase k j hj (sourceWidth cfg m)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) σ)
        (copiedSurvivingPermutation k j (sourceWidth cfg m) ρ) p χ a ζ P s t u
        (.inr (copiedRetiredOutside cfg m j hj.le true a₀ b)) (.inl (copiedBulk cfg m j z)) := by
  obtain ⟨z,hz⟩ := exists_bulk_code_change cfg m j σ ρ hσ hρ hcode
  exact ⟨z,copied_matching_surviving_squarePhase cfg m j hj σ ρ
    (fun i hi=>(hσ i).mpr hi) (fun i hi=>(hρ i).mpr hi) z hz p hc χ hχ a ζ hζ P s t u ht hu⟩

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
