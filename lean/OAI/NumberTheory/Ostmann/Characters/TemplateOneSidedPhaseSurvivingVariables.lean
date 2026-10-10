import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingSquare

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
attribute [local instance] Classical.propDecidable

theorem survivingPhasePair_twoPrimeAssignment (k j : ℕ) (hj : j<k) (width : Role → ℕ)
    (σ ρ : Equiv.Perm (SurvivingPrimeIndex k j width))
    (p : SurvivingPrimeIndex k j width → ℕ)
    (L S : SurvivingPrimeIndex k j width) (hLS : L ≠ S) (q r : ℕ)
    [∀i,Fact (twoPrimeAssignment p L S q r i).Prime]
    (hc : Pairwise (fun i h => (twoPrimeAssignment p L S q r i).Coprime (twoPrimeAssignment p L S q r h)))
    (χ : SurvivingPrimeIndex k j width → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : SurvivingPrimeIndex k j width → (q : ℕ) → ZMod q) (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ) (P : ℕ) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (hrev : survivingDifferenceGraph k j hj width σ ρ L S = 0) :
    survivingPhasePair k j hj width σ ρ (twoPrimeAssignment p L S q r) χ a ζ P s t u =
      indexedLongUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S q *
      indexedShortUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S r *
        χ S r q ^ survivingDifferenceGraph k j hj width σ ρ S L := by
  rw [survivingPhasePair_eq_graph k j hj width σ ρ _ hc χ a ζ P s t u]
  exact indexedPrimeGraphPhase_oneSided (survivingDifferenceGraph k j hj width σ ρ) p χ
    (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S hLS
    (survivingDifferenceGraph_self k j hj width σ ρ L) (survivingDifferenceGraph_self k j hj width σ ρ S) hrev q r

theorem survivingPhasePair_twoPrimeAssignment_unary_norms (k j : ℕ) (hj : j<k) (width : Role → ℕ)
    (σ ρ : Equiv.Perm (SurvivingPrimeIndex k j width))
    (p : SurvivingPrimeIndex k j width → ℕ)
    (L S : SurvivingPrimeIndex k j width) (hLS : L ≠ S) (q r : ℕ)
    [∀i,Fact (twoPrimeAssignment p L S q r i).Prime]
    (χ : SurvivingPrimeIndex k j width → (q : ℕ) → MulChar (ZMod q) ℂ) (hχ : ∀i,χ i (twoPrimeAssignment p L S q r i) ≠ 1)
    (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ) (hζ : ∀i q,‖ζ i q‖≤1) (P : ℕ) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (ht : ∀i,HistoryFrequencyUnits (twoPrimeAssignment p L S q r i) j s t)
    (hu : ∀i,HistoryFrequencyUnits (twoPrimeAssignment p L S q r i) j s u) :
    ‖indexedLongUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S q‖ ≤ 1 ∧
    ‖indexedShortUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S r‖ ≤ 1 := by
  have hh := survivingPhasePair_unary_norms k j hj width σ ρ (twoPrimeAssignment p L S q r) χ hχ ζ hζ P s t u ht hu L S
  simpa only [twoPrimeAssignment_long p L S hLS q r,twoPrimeAssignment_short,
    indexedLongUnary_twoPrimeAssignment,indexedShortUnary_twoPrimeAssignment] using hh

theorem survivingPhasePair_twoPrimeAssignment_square (k j : ℕ) (hj : j<k) (width : Role → ℕ)
    (σ ρ : Equiv.Perm (SurvivingPrimeIndex k j width))
    (p : SurvivingPrimeIndex k j width → ℕ)
    (L S : SurvivingPrimeIndex k j width) (hLS : L ≠ S) (q r : ℕ)
    [∀i,Fact (twoPrimeAssignment p L S q r i).Prime]
    (hc : Pairwise (fun i h => (twoPrimeAssignment p L S q r i).Coprime (twoPrimeAssignment p L S q r h)))
    (χ : SurvivingPrimeIndex k j width → (q : ℕ) → MulChar (ZMod q) ℂ) (hχ : ∀i,2 < orderOf (χ i (twoPrimeAssignment p L S q r i)))
    (a : SurvivingPrimeIndex k j width → (q : ℕ) → ZMod q) (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ) (hζ : ∀i q,‖ζ i q‖≤1) (P : ℕ) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (ht : ∀i,HistoryFrequencyUnits (twoPrimeAssignment p L S q r i) j s t)
    (hu : ∀i,HistoryFrequencyUnits (twoPrimeAssignment p L S q r i) j s u)
    (positive : Bool) (hforward : survivingDifferenceGraph k j hj width σ ρ S L = if positive then 2 else -2)
    (hrev : survivingDifferenceGraph k j hj width σ ρ L S = 0) :
    survivingPhasePair k j hj width σ ρ (twoPrimeAssignment p L S q r) χ a ζ P s t u =
      indexedLongUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S q *
      indexedShortUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S r *
        exposedCharacter (χ S r) positive q ∧
    ‖indexedLongUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S q‖ ≤ 1 ∧
    ‖indexedShortUnary (survivingDifferenceGraph k j hj width σ ρ) p χ (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S r‖ ≤ 1 ∧
    exposedCharacter (χ S r) positive ≠ 1 := by
  have hne : ∀i,χ i (twoPrimeAssignment p L S q r i) ≠ 1 := by
    intro i he
    have hh := hχ i
    rw [he,orderOf_one] at hh
    norm_num at hh
  have he := survivingPhasePair_twoPrimeAssignment k j hj width σ ρ p L S hLS q r hc χ a ζ P s t u hrev
  have hnorm := survivingPhasePair_twoPrimeAssignment_unary_norms k j hj width σ ρ p L S hLS q r χ hne ζ hζ P s t u ht hu
  refine ⟨?_,hnorm.1,hnorm.2,exposedCharacter_ne_one _ ?_ positive⟩
  · simpa only [exposedCharacter_apply,hforward] using he
  · exact (twoPrimeAssignment_short p L S q r) ▸ hχ S

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
