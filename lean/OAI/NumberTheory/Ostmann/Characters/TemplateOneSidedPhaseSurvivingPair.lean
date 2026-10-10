import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingSplit
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingUnary

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
attribute [local instance] Classical.propDecidable

def survivingDifferenceGraph (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (σ ρ : Equiv.Perm (SurvivingPrimeIndex k j width)) :=
  fun i h=>permutedGraph (survivingGraph k j hj width) σ i h-
    permutedGraph (survivingGraph k j hj width) ρ i h

@[simp] theorem survivingDifferenceGraph_self (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (σ ρ : Equiv.Perm (SurvivingPrimeIndex k j width)) (i : SurvivingPrimeIndex k j width) :
    survivingDifferenceGraph k j hj width σ ρ i i=0 := by
  simp [survivingDifferenceGraph,permutedGraph]

theorem decoratedSurvivingPhase_permutation (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (σ : Equiv.Perm (SurvivingPrimeIndex k j width))
    (p : SurvivingPrimeIndex k j width → ℕ) [∀i,Fact (p i).Prime]
    (χ : SurvivingPrimeIndex k j width → (q:ℕ) → MulChar (ZMod q) ℂ)
    (a : SurvivingPrimeIndex k j width → (q:ℕ) → ZMod q)
    (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ)
    (P : ℕ) (s : ℤ) (t : HistoryReconstruction.Tree j) :
    decoratedSurvivingPhase k j hj width σ p χ a ζ P s t =
      survivingTranslationProduct p (fun i=>a i (p i)) P s *
        primeGraphPhase (permutedGraph (survivingGraph k j hj width) σ) p
          (fun i=>χ i (p i)) (fun i=>survivingUnary k j hj width χ ζ σ P s t i (p i)) := by
  have hζ : (∏i,ζ i (p (σ.symm i)))=∏i,ζ (σ i) (p i) := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.prod_comp σ (fun i=>ζ i (p (σ.symm i)))).symm
  rw [decoratedSurvivingPhase,hζ,actualPivotSurviving_permutation k j hj width σ p
    (fun i=>χ i (p i)) (fun i=>a i (p i)) P s t]
  simp only [primeGraphPhase,survivingUnary,historyUnaryAt_prime,Finset.prod_mul_distrib]
  ring

def survivingPhasePair (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (σ ρ : Equiv.Perm (SurvivingPrimeIndex k j width))
    (p : SurvivingPrimeIndex k j width → ℕ) [∀i,Fact (p i).Prime]
    (χ : SurvivingPrimeIndex k j width → (q:ℕ) → MulChar (ZMod q) ℂ)
    (a : SurvivingPrimeIndex k j width → (q:ℕ) → ZMod q)
    (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ)
    (P : ℕ) (s : ℤ) (t u : HistoryReconstruction.Tree j) : ℂ :=
  decoratedSurvivingPhase k j hj width σ p χ a ζ P s t *
    conj (decoratedSurvivingPhase k j hj width ρ p χ a ζ P s u)

theorem survivingPhasePair_eq_graph (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (σ ρ : Equiv.Perm (SurvivingPrimeIndex k j width))
    (p : SurvivingPrimeIndex k j width → ℕ) [∀i,Fact (p i).Prime]
    (hc : Pairwise (fun i h=>(p i).Coprime (p h)))
    (χ : SurvivingPrimeIndex k j width → (q:ℕ) → MulChar (ZMod q) ℂ)
    (a : SurvivingPrimeIndex k j width → (q:ℕ) → ZMod q)
    (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ)
    (P : ℕ) (s : ℤ) (t u : HistoryReconstruction.Tree j) :
    survivingPhasePair k j hj width σ ρ p χ a ζ P s t u =
      primeGraphPhase (survivingDifferenceGraph k j hj width σ ρ) p (fun i=>χ i (p i))
        (fun i=>pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u i (p i)) := by
  rw [survivingPhasePair,decoratedSurvivingPhase_permutation,decoratedSurvivingPhase_permutation,map_mul]
  rw [show ∀ A B C D : ℂ,(A*B)*(C*D)=(A*C)*(B*D) by intros;ring,
    survivingTranslationProduct_mul_conj,one_mul]
  exact primeGraphPhase_mul_conj
    (permutedGraph (survivingGraph k j hj width) σ)
    (permutedGraph (survivingGraph k j hj width) ρ)
    (fun i=>survivingGraph_self k j hj width (σ i))
    (fun i=>survivingGraph_self k j hj width (ρ i)) p hc (fun i=>χ i (p i))
    (fun i=>survivingUnary k j hj width χ ζ σ P s t i (p i))
    (fun i=>survivingUnary k j hj width χ ζ ρ P s u i (p i))

theorem survivingPhasePair_oneSided (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (σ ρ : Equiv.Perm (SurvivingPrimeIndex k j width))
    (p : SurvivingPrimeIndex k j width → ℕ) [∀i,Fact (p i).Prime]
    (hc : Pairwise (fun i h=>(p i).Coprime (p h)))
    (χ : SurvivingPrimeIndex k j width → (q:ℕ) → MulChar (ZMod q) ℂ)
    (a : SurvivingPrimeIndex k j width → (q:ℕ) → ZMod q)
    (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ)
    (P : ℕ) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (L S : SurvivingPrimeIndex k j width) (hLS : L≠S)
    (hrev : survivingDifferenceGraph k j hj width σ ρ L S=0) :
    survivingPhasePair k j hj width σ ρ p χ a ζ P s t u =
      indexedLongUnary (survivingDifferenceGraph k j hj width σ ρ) p χ
        (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S (p L) *
      indexedShortUnary (survivingDifferenceGraph k j hj width σ ρ) p χ
        (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S (p S) *
      χ S (p S) (p L) ^ survivingDifferenceGraph k j hj width σ ρ S L := by
  rw [survivingPhasePair_eq_graph k j hj width σ ρ p hc χ a ζ P s t u]
  have hh := indexedPrimeGraphPhase_oneSided (survivingDifferenceGraph k j hj width σ ρ) p χ
    (pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u) L S hLS
    (survivingDifferenceGraph_self k j hj width σ ρ L)
    (survivingDifferenceGraph_self k j hj width σ ρ S) hrev (p L) (p S)
  have he : twoPrimeAssignment p L S (p L) (p S)=p := by
    simp only [twoPrimeAssignment,Function.update_eq_self]
  rw [he] at hh
  exact hh

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
