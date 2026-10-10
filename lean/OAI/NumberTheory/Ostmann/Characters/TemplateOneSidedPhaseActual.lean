import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSplitNorm
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseUnary

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
attribute [local instance] Classical.propDecidable

def differenceGraph (k j : ℕ) (width : Role → ℕ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width)) :=
  fun i h=>permutedGraph (constituentGraph k j width) σ i h-
    permutedGraph (constituentGraph k j width) ρ i h

@[simp] theorem differenceGraph_self (k j : ℕ) (width : Role → ℕ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width)) (i : (schedule k j).Constituent width) :
    differenceGraph k j width σ ρ i i=0 := by
  simp [differenceGraph,permutedGraph,constituentGraph,liftGraph]

def phasePair (k j : ℕ) (width : Role → ℕ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (p : (schedule k j).Constituent width → ℕ) [∀i,Fact (p i).Prime]
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (a : (q : ℕ) → ZMod q)
    (s : ℤ) (t u : HistoryReconstruction.Tree j) : ℂ :=
  actualHistoryPhase k j width (fun i=>p (σ.symm i))
      (fun i=>χ (p (σ.symm i))) (fun i=>a (p (σ.symm i))) s t *
    conj (actualHistoryPhase k j width (fun i=>p (ρ.symm i))
      (fun i=>χ (p (ρ.symm i))) (fun i=>a (p (ρ.symm i))) s u)

theorem phasePair_oneSided (k j : ℕ) (width : Role → ℕ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (p : (schedule k j).Constituent width → ℕ) [∀i,Fact (p i).Prime]
    (hc : Pairwise (fun i h=>(p i).Coprime (p h)))
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (hχ : ∀i,χ (p i)≠1)
    (a : (q : ℕ) → ZMod q) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (hu : ∀i,HistoryFrequencyUnits (p i) j s u)
    (L S : (schedule k j).Constituent width) (hLS : L≠S)
    (hrev : differenceGraph k j width σ ρ L S=0) :
    phasePair k j width σ ρ p χ a s t u =
      longUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S (p L) *
      shortUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S (p S) *
      χ (p S) (p L) ^ differenceGraph k j width σ ρ S L := by
  rw [phasePair,actualHistoryPhase_pair_eq_quotient k j width σ ρ p hc χ hχ a s t u hu]
  have hh := primeGraphPhase_oneSided (differenceGraph k j width σ ρ) p χ
    (quotientUnary k j width χ σ ρ s t u) L S hLS
    (differenceGraph_self k j width σ ρ L) (differenceGraph_self k j width σ ρ S) hrev (p L) (p S)
  have he : twoPrimeAssignment p L S (p L) (p S)=p := by
    simp only [twoPrimeAssignment,Function.update_eq_self]
  rw [he] at hh
  exact hh

theorem phasePair_unary_norms (k j : ℕ) (width : Role → ℕ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (p : (schedule k j).Constituent width → ℕ) [∀i,Fact (p i).Prime]
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (hχ : ∀i,χ (p i)≠1)
    (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (ht : ∀i,HistoryFrequencyUnits (p i) j s t) (hu : ∀i,HistoryFrequencyUnits (p i) j s u)
    (L S : (schedule k j).Constituent width) :
    ‖longUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S (p L)‖ ≤ 1 ∧
    ‖shortUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S (p S)‖ ≤ 1 := by
  have hν (i : (schedule k j).Constituent width) :
      ‖quotientUnary k j width χ σ ρ s t u i (p i)‖ ≤ 1 :=
    (norm_quotientUnary k j width χ σ ρ s t u i (p i) (hχ i) (ht i) (hu i)).le
  exact ⟨norm_longUnary_le_one _ _ _ _ L S (fun i _=>Fact.out) (fun i _=>hν i) _ Fact.out (hν L),
    norm_shortUnary_le_one _ _ _ _ L S (fun i _=>Fact.out) _ Fact.out (hν S)⟩

@[simp] theorem exposedCharacter_apply {q : ℕ} (χ : MulChar (ZMod q) ℂ)
    (positive : Bool) (n : ℕ) :
    exposedCharacter χ positive n=χ n^(if positive then (2:ℤ) else -2) := by
  cases positive <;>
    simp only [exposedCharacter,Bool.false_eq_true,ite_false,ite_true,
      MulChar.inv_apply_eq_inv',MulChar.pow_apply' χ (by decide : (2:ℕ)≠0),zpow_neg,zpow_ofNat]

theorem phasePair_square (k j : ℕ) (width : Role → ℕ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (p : (schedule k j).Constituent width → ℕ) [∀i,Fact (p i).Prime]
    (hc : Pairwise (fun i h=>(p i).Coprime (p h)))
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (hχ : ∀i,2<orderOf (χ (p i)))
    (a : (q : ℕ) → ZMod q) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (ht : ∀i,HistoryFrequencyUnits (p i) j s t) (hu : ∀i,HistoryFrequencyUnits (p i) j s u)
    (L S : (schedule k j).Constituent width) (hLS : L≠S)
    (hforward : differenceGraph k j width σ ρ S L=2 ∨ differenceGraph k j width σ ρ S L= -2)
    (hrev : differenceGraph k j width σ ρ L S=0) :
    ∃positive : Bool,
      phasePair k j width σ ρ p χ a s t u =
        longUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S (p L) *
        shortUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S (p S) *
          exposedCharacter (χ (p S)) positive (p L) ∧
      ‖longUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S (p L)‖ ≤ 1 ∧
      ‖shortUnary (differenceGraph k j width σ ρ) p χ (quotientUnary k j width χ σ ρ s t u) L S (p S)‖ ≤ 1 ∧
      exposedCharacter (χ (p S)) positive≠1 := by
  have hne : ∀i,χ (p i)≠1 := by
    intro i he
    have h := hχ i
    rw [he,orderOf_one] at h
    norm_num at h
  have he := phasePair_oneSided k j width σ ρ p hc χ hne a s t u hu L S hLS hrev
  have hn := phasePair_unary_norms k j width σ ρ p χ hne s t u ht hu L S
  rcases hforward with hf | hf
  · refine ⟨true,?_,hn.1,hn.2,exposedCharacter_ne_one _ (hχ S) true⟩
    simpa only [exposedCharacter_apply,ite_true,hf] using he
  · refine ⟨false,?_,hn.1,hn.2,exposedCharacter_ne_one _ (hχ S) false⟩
    simpa only [exposedCharacter_apply,Bool.false_eq_true,ite_false,hf] using he

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
