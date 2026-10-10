import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingPair
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingSplitNorm

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
attribute [local instance] Classical.propDecidable

theorem survivingPhasePair_unary_norms (k j : ℕ) (hj : j<k) (width : Role → ℕ)
    (σ ρ : Equiv.Perm (SurvivingPrimeIndex k j width))
    (p : SurvivingPrimeIndex k j width → ℕ) [∀i,Fact (p i).Prime]
    (χ : SurvivingPrimeIndex k j width → (q : ℕ) → MulChar (ZMod q) ℂ) (hχ : ∀i,χ i (p i)≠1)
    (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ) (hζ : ∀i q,‖ζ i q‖≤1)
    (P : ℕ) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (ht : ∀i,HistoryFrequencyUnits (p i) j s t) (hu : ∀i,HistoryFrequencyUnits (p i) j s u)
    (L S : SurvivingPrimeIndex k j width) :
    ‖indexedLongUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S (p L)‖ ≤ 1 ∧
    ‖indexedShortUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S (p S)‖ ≤ 1 := by
  have hν (i : SurvivingPrimeIndex k j width) :
      ‖pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u i (p i)‖ ≤ 1 :=
    norm_pairedSurvivingUnary_le k j hj width χ ζ σ ρ P s t u i (p i) (hχ i) (hζ _ _) (hζ _ _) (ht i) (hu i)
  exact ⟨norm_indexedLongUnary_le_one _ _ _ _ L S (fun i _=>Fact.out) (fun i _=>hν i) _ Fact.out (hν L),
    norm_indexedShortUnary_le_one _ _ _ _ L S (fun i _=>Fact.out) _ Fact.out (hν S)⟩

def SurvivingSquarePhase (k j : ℕ) (hj : j<k) (width : Role → ℕ)
    (σ ρ : Equiv.Perm (SurvivingPrimeIndex k j width))
    (p : SurvivingPrimeIndex k j width → ℕ) [∀i,Fact (p i).Prime]
    (χ : SurvivingPrimeIndex k j width → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : SurvivingPrimeIndex k j width → (q : ℕ) → ZMod q)
    (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ)
    (P : ℕ) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (L S : SurvivingPrimeIndex k j width) : Prop :=
    ∃positive : Bool,
      survivingPhasePair k j hj width σ ρ p χ a ζ P s t u =
        indexedLongUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S (p L) *
        indexedShortUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S (p S) *
          exposedCharacter (χ S (p S)) positive (p L) ∧
      ‖indexedLongUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S (p L)‖ ≤ 1 ∧
      ‖indexedShortUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S (p S)‖ ≤ 1 ∧
      exposedCharacter (χ S (p S)) positive≠1

theorem survivingPhasePair_square (k j : ℕ) (hj : j<k) (width : Role → ℕ)
    (σ ρ : Equiv.Perm (SurvivingPrimeIndex k j width))
    (p : SurvivingPrimeIndex k j width → ℕ) [∀i,Fact (p i).Prime]
    (hc : Pairwise (fun i h=>(p i).Coprime (p h)))
    (χ : SurvivingPrimeIndex k j width → (q : ℕ) → MulChar (ZMod q) ℂ) (hχ : ∀i,2<orderOf (χ i (p i)))
    (a : SurvivingPrimeIndex k j width → (q : ℕ) → ZMod q) (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ) (hζ : ∀i q,‖ζ i q‖≤1)
    (P : ℕ) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (ht : ∀i,HistoryFrequencyUnits (p i) j s t) (hu : ∀i,HistoryFrequencyUnits (p i) j s u)
    (L S : SurvivingPrimeIndex k j width) (hLS : L≠S)
    (hforward : survivingDifferenceGraph k j hj width σ ρ S L=2 ∨ survivingDifferenceGraph k j hj width σ ρ S L= -2)
    (hrev : survivingDifferenceGraph k j hj width σ ρ L S=0) :
    ∃positive : Bool,
      survivingPhasePair k j hj width σ ρ p χ a ζ P s t u =
        indexedLongUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S (p L) *
        indexedShortUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S (p S) *
          exposedCharacter (χ S (p S)) positive (p L) ∧
      ‖indexedLongUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S (p L)‖ ≤ 1 ∧
      ‖indexedShortUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S (p S)‖ ≤ 1 ∧
      exposedCharacter (χ S (p S)) positive≠1 := by
  have hne : ∀i,χ i (p i)≠1 := by
    intro i he
    have h := hχ i
    rw [he,orderOf_one] at h
    norm_num at h
  have he := survivingPhasePair_oneSided k j hj width σ ρ p hc χ a ζ P s t u L S hLS hrev
  have hn := survivingPhasePair_unary_norms k j hj width σ ρ p χ hne ζ hζ P s t u ht hu L S
  rcases hforward with hf | hf
  · refine ⟨true,?_,hn.1,hn.2,exposedCharacter_ne_one _ (hχ S) true⟩
    simpa only [exposedCharacter_apply,ite_true,hf] using he
  · refine ⟨false,?_,hn.1,hn.2,exposedCharacter_ne_one _ (hχ S) false⟩
    simpa only [exposedCharacter_apply,Bool.false_eq_true,ite_false,hf] using he

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
