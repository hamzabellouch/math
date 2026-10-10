import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingReindex

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
attribute [local instance] Classical.propDecidable

def survivingGraph (k j : ℕ) (hj : j<k) (width : Role→ℕ) :
    SurvivingPrimeIndex k j width → SurvivingPrimeIndex k j width → ℤ :=
  fun i h=>constituentGraph k j width (scheduledConstituentInput k j hj width (.inr i))
    (scheduledConstituentInput k j hj width (.inr h))

def survivingPivotExponent (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (i : SurvivingPrimeIndex k j width) : ℤ :=
  collapsedConstituentGraph (schedule k j) j width (pivotSlot k j hj)
    (graph k j) (intraGraph k j) (some i) none

@[simp] theorem survivingGraph_self (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (i : SurvivingPrimeIndex k j width) : survivingGraph k j hj width i i=0 := by
  simp [survivingGraph,constituentGraph,liftGraph]

def survivingUnary (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (χ : SurvivingPrimeIndex k j width → (q:ℕ) → MulChar (ZMod q) ℂ)
    (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ)
    (σ : Equiv.Perm (SurvivingPrimeIndex k j width)) (P : ℕ)
    (s : ℤ) (t : HistoryReconstruction.Tree j) (i : SurvivingPrimeIndex k j width) (q : ℕ) : ℂ :=
  ζ (σ i) q * historyUnaryAt k j width (χ i) s t
    (scheduledConstituentInput k j hj width (.inr (σ i))) q *
    χ i q P ^ survivingPivotExponent k j hj width (σ i)

def pairedSurvivingUnary (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (χ : SurvivingPrimeIndex k j width → (q:ℕ) → MulChar (ZMod q) ℂ)
    (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ)
    (σ ρ : Equiv.Perm (SurvivingPrimeIndex k j width)) (P : ℕ)
    (s : ℤ) (t u : HistoryReconstruction.Tree j) (i : SurvivingPrimeIndex k j width) (q : ℕ) : ℂ :=
  survivingUnary k j hj width χ ζ σ P s t i q *
    conj (survivingUnary k j hj width χ ζ ρ P s u i q)

theorem norm_survivingUnary_le (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (χ : SurvivingPrimeIndex k j width → (q:ℕ) → MulChar (ZMod q) ℂ)
    (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ)
    (σ : Equiv.Perm (SurvivingPrimeIndex k j width)) (P : ℕ)
    (s : ℤ) (t : HistoryReconstruction.Tree j) (i : SurvivingPrimeIndex k j width)
    (q : ℕ) [Fact q.Prime] (hχ : χ i q≠1) (hζ : ‖ζ (σ i) q‖≤1)
    (ht : HistoryFrequencyUnits q j s t) :
    ‖survivingUnary k j hj width χ ζ σ P s t i q‖≤1 := by
  simp only [survivingUnary,historyUnaryAt_prime,norm_mul,
    norm_actualHistoryUnary k width (χ i q) hχ j s t ht,mul_one]
  exact (mul_le_mul hζ (norm_character_zpow_le_one (χ i q) _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem norm_pairedSurvivingUnary_le (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (χ : SurvivingPrimeIndex k j width → (q:ℕ) → MulChar (ZMod q) ℂ)
    (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ)
    (σ ρ : Equiv.Perm (SurvivingPrimeIndex k j width)) (P : ℕ)
    (s : ℤ) (t u : HistoryReconstruction.Tree j) (i : SurvivingPrimeIndex k j width)
    (q : ℕ) [Fact q.Prime] (hχ : χ i q≠1)
    (hζσ : ‖ζ (σ i) q‖≤1) (hζρ : ‖ζ (ρ i) q‖≤1)
    (ht : HistoryFrequencyUnits q j s t) (hu : HistoryFrequencyUnits q j s u) :
    ‖pairedSurvivingUnary k j hj width χ ζ σ ρ P s t u i q‖≤1 := by
  rw [pairedSurvivingUnary,norm_mul,Complex.norm_conj]
  exact (mul_le_mul (norm_survivingUnary_le k j hj width χ ζ σ P s t i q hχ hζσ ht)
    (norm_survivingUnary_le k j hj width χ ζ ρ P s u i q hχ hζρ hu) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

def decoratedSurvivingPhase (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (σ : Equiv.Perm (SurvivingPrimeIndex k j width))
    (p : SurvivingPrimeIndex k j width → ℕ) [∀i,Fact (p i).Prime]
    (χ : SurvivingPrimeIndex k j width → (q:ℕ) → MulChar (ZMod q) ℂ)
    (a : SurvivingPrimeIndex k j width → (q:ℕ) → ZMod q)
    (ζ : SurvivingPrimeIndex k j width → ℕ → ℂ)
    (P : ℕ) (s : ℤ) (t : HistoryReconstruction.Tree j) : ℂ :=
  (∏i,ζ i (p (σ.symm i))) *
    actualPivotSurviving k j hj width (fun i=>p (σ.symm i))
      (fun i=>χ (σ.symm i) (p (σ.symm i))) (fun i=>a (σ.symm i) (p (σ.symm i))) P s t

theorem actualPivotSurviving_permutation (k j : ℕ) (hj : j<k) (width : Role→ℕ)
    (σ : Equiv.Perm (SurvivingPrimeIndex k j width))
    (p : SurvivingPrimeIndex k j width → ℕ) [∀i,Fact (p i).Prime]
    (χ : ∀i,MulChar (ZMod (p i)) ℂ) (a : ∀i,ZMod (p i))
    (P : ℕ) (s : ℤ) (t : HistoryReconstruction.Tree j) :
    actualPivotSurviving k j hj width (fun i=>p (σ.symm i))
      (fun i=>χ (σ.symm i)) (fun i=>a (σ.symm i)) P s t =
    survivingTranslationProduct p a P s *
      primeGraphPhase (permutedGraph (survivingGraph k j hj width) σ) p χ
        (fun i=>actualHistoryUnary k width (χ i) j s t
          (scheduledConstituentInput k j hj width (.inr (σ i))) *
          χ i P ^ survivingPivotExponent k j hj width (σ i)) := by
  have h := survivingPrimeRows_permutation σ p χ a
      (fun i=>actualHistoryUnary k width (χ (σ.symm i)) j s t
        (scheduledConstituentInput k j hj width (.inr i)))
      (survivingGraph k j hj width) (survivingPivotExponent k j hj width) P s
  have he (i : SurvivingPrimeIndex k j width) :
      actualHistoryUnary k width (χ (σ.symm (σ i))) j s t
          (scheduledConstituentInput k j hj width (.inr (σ i))) =
      actualHistoryUnary k width (χ i) j s t
          (scheduledConstituentInput k j hj width (.inr (σ i))) := by
    exact congrArg (fun z=>actualHistoryUnary k width (χ z) j s t
      (scheduledConstituentInput k j hj width (.inr (σ i)))) (σ.symm_apply_apply i)
  simp_rw [he] at h
  exact h

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
