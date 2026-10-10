import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
attribute [local instance] Classical.propDecidable

theorem phasePair_twoPrimeAssignment (k j : ℕ) (width : Role → ℕ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (p : (schedule k j).Constituent width → ℕ)
    (L S : (schedule k j).Constituent width) (hLS : L ≠ S) (q r : ℕ)
    [∀i,Fact (twoPrimeAssignment p L S q r i).Prime]
    (hc : Pairwise (fun i h => (twoPrimeAssignment p L S q r i).Coprime (twoPrimeAssignment p L S q r h)))
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (hχ : ∀i,χ (twoPrimeAssignment p L S q r i) ≠ 1)
    (a : (q : ℕ) → ZMod q) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (hu : ∀i,HistoryFrequencyUnits (twoPrimeAssignment p L S q r i) j s u)
    (hrev : differenceGraph k j width σ ρ L S = 0) :
    phasePair k j width σ ρ (twoPrimeAssignment p L S q r) χ a s t u =
      longUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S q *
      shortUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S r *
        χ r q ^ differenceGraph k j width σ ρ S L := by
  rw [phasePair,actualHistoryPhase_pair_eq_quotient k j width σ ρ _ hc χ hχ a s t u hu]
  exact primeGraphPhase_oneSided (differenceGraph k j width σ ρ) p χ
    (quotientUnary k j width χ σ ρ s t u) L S hLS
    (differenceGraph_self k j width σ ρ L) (differenceGraph_self k j width σ ρ S) hrev q r

theorem phasePair_twoPrimeAssignment_unary_norms (k j : ℕ) (width : Role → ℕ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (p : (schedule k j).Constituent width → ℕ)
    (L S : (schedule k j).Constituent width) (hLS : L ≠ S) (q r : ℕ)
    [∀i,Fact (twoPrimeAssignment p L S q r i).Prime]
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (hχ : ∀i,χ (twoPrimeAssignment p L S q r i) ≠ 1)
    (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (ht : ∀i,HistoryFrequencyUnits (twoPrimeAssignment p L S q r i) j s t)
    (hu : ∀i,HistoryFrequencyUnits (twoPrimeAssignment p L S q r i) j s u) :
    ‖longUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S q‖ ≤ 1 ∧
    ‖shortUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S r‖ ≤ 1 := by
  have hh := phasePair_unary_norms k j width σ ρ (twoPrimeAssignment p L S q r) χ hχ s t u ht hu L S
  simpa only [twoPrimeAssignment_long p L S hLS q r,twoPrimeAssignment_short,
    longUnary_twoPrimeAssignment,shortUnary_twoPrimeAssignment] using hh

theorem phasePair_twoPrimeAssignment_square (k j : ℕ) (width : Role → ℕ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (p : (schedule k j).Constituent width → ℕ)
    (L S : (schedule k j).Constituent width) (hLS : L ≠ S) (q r : ℕ)
    [∀i,Fact (twoPrimeAssignment p L S q r i).Prime]
    (hc : Pairwise (fun i h => (twoPrimeAssignment p L S q r i).Coprime (twoPrimeAssignment p L S q r h)))
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (hχ : ∀i,2 < orderOf (χ (twoPrimeAssignment p L S q r i)))
    (a : (q : ℕ) → ZMod q) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (ht : ∀i,HistoryFrequencyUnits (twoPrimeAssignment p L S q r i) j s t)
    (hu : ∀i,HistoryFrequencyUnits (twoPrimeAssignment p L S q r i) j s u)
    (positive : Bool) (hforward : differenceGraph k j width σ ρ S L = if positive then 2 else -2)
    (hrev : differenceGraph k j width σ ρ L S = 0) :
    phasePair k j width σ ρ (twoPrimeAssignment p L S q r) χ a s t u =
      longUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S q *
      shortUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S r *
        exposedCharacter (χ r) positive q ∧
    ‖longUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S q‖ ≤ 1 ∧
    ‖shortUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S r‖ ≤ 1 ∧
    exposedCharacter (χ r) positive ≠ 1 := by
  have hne : ∀i,χ (twoPrimeAssignment p L S q r i) ≠ 1 := by
    intro i he
    have hh := hχ i
    rw [he,orderOf_one] at hh
    norm_num at hh
  have he := phasePair_twoPrimeAssignment k j width σ ρ p L S hLS q r hc χ hne a s t u hu hrev
  have hnorm := phasePair_twoPrimeAssignment_unary_norms k j width σ ρ p L S hLS q r χ hne s t u ht hu
  refine ⟨?_,hnorm.1,hnorm.2,exposedCharacter_ne_one _ ?_ positive⟩
  · simpa only [exposedCharacter_apply,hforward] using he
  · exact (twoPrimeAssignment_short p L S q r) ▸ hχ S

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
