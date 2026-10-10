import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitSource
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingAction
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseUnitsBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries
attribute [local instance] Classical.propDecidable

def extendCharacterData {I : Type*} {Q : ℕ}
    (χ : I → (p : PrimeUpTo Q) → MulChar (ZMod p.val) ℂ) (i : I) (q : ℕ) : MulChar (ZMod q) ℂ :=
  if h : q ∈ Q.primesLE then χ i ⟨q,h⟩ else 1

@[simp] theorem extendCharacterData_prime {I : Type*} {Q : ℕ}
    (χ : I → (p : PrimeUpTo Q) → MulChar (ZMod p.val) ℂ) (i : I) (p : PrimeUpTo Q) :
    extendCharacterData χ i p.val = χ i p := by
  simp only [extendCharacterData, dite_eq_left p.property]

def extendTranslationData {I : Type*} {Q : ℕ}
    (a : I → (p : PrimeUpTo Q) → ZMod p.val) (i : I) (q : ℕ) : ZMod q :=
  if h : q ∈ Q.primesLE then a i ⟨q,h⟩ else 0

@[simp] theorem extendTranslationData_prime {I : Type*} {Q : ℕ}
    (a : I → (p : PrimeUpTo Q) → ZMod p.val) (i : I) (p : PrimeUpTo Q) :
    extendTranslationData a i p.val = a i p := by
  simp only [extendTranslationData, dite_eq_left p.property]

def finiteSurvivingCharacters (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q) :=
  extendCharacterData (fun i : SurvivingPrimeIndex k j width =>
    χ (scheduledConstituentInput k j hj width (.inr i)))

def finiteSurvivingTranslations (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (a : PrimeTranslationData (schedule k j) width Q) :=
  extendTranslationData (fun i : SurvivingPrimeIndex k j width =>
    a (scheduledConstituentInput k j hj width (.inr i)))

def finiteSurvivingUnits (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q) :=
  extendUnitData (fun i : SurvivingPrimeIndex k j width =>
    ζ (scheduledConstituentInput k j hj width (.inr i)))

def sampledDecoratedSurvivor (k j : ℕ) (hj : j<k) (width : Role→ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (x : SurvivingPrimeIndex k j width → PrimeUpTo Q)
    (P : ℕ+) (s : ℤ) (t : HistoryReconstruction.Tree j) : ℂ :=
  letI : ∀i,Fact (x i).val.Prime := fun i => ⟨primeUpTo_prime (x i)⟩
  (∏i,ζ (scheduledConstituentInput k j hj width (.inr i)) (x i)) *
    actualPivotSurviving k j hj width (fun i => (x i).val)
      (fun i => χ (scheduledConstituentInput k j hj width (.inr i)) (x i))
      (fun i => a (scheduledConstituentInput k j hj width (.inr i)) (x i)) P s t

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
