import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorSources
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitAmplitude

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open Construction Preliminaries

def scheduledCharacterData (k : ℕ) (width : Role → ℕ) {Q : ℕ}
    (χ₀ : PrimeCharacterData (schedule k 0) width Q) (j : ℕ) :
    PrimeCharacterData (schedule k j) width Q :=
  fun i => χ₀ (scheduledConstituentOrigin k width j i)

def scheduledTranslationData (k : ℕ) (width : Role → ℕ) {Q : ℕ}
    (a₀ : PrimeTranslationData (schedule k 0) width Q) (j : ℕ) :
    PrimeTranslationData (schedule k j) width Q :=
  fun i => a₀ (scheduledConstituentOrigin k width j i)

@[simp] theorem scheduledCharacterData_zero (k : ℕ) (width : Role → ℕ) {Q : ℕ}
    (χ₀ : PrimeCharacterData (schedule k 0) width Q) :
    scheduledCharacterData k width χ₀ 0 = χ₀ := rfl

@[simp] theorem scheduledTranslationData_zero (k : ℕ) (width : Role → ℕ) {Q : ℕ}
    (a₀ : PrimeTranslationData (schedule k 0) width Q) :
    scheduledTranslationData k width a₀ 0 = a₀ := rfl

@[simp] theorem scheduledCharacterData_succ (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (χ₀ : PrimeCharacterData (schedule k 0) width Q) :
    scheduledCharacterData k width χ₀ (j+1) =
      fun i => scheduledCharacterData k width χ₀ j
        (previousConstituent (schedule k j) j width i) := rfl

@[simp] theorem scheduledTranslationData_succ (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (a₀ : PrimeTranslationData (schedule k 0) width Q) :
    scheduledTranslationData k width a₀ (j+1) =
      fun i => scheduledTranslationData k width a₀ j
        (previousConstituent (schedule k j) j width i) := rfl

theorem scheduledCharacterData_nonprincipal (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E₀ : (schedule k 0).Constituent width → Finset (PrimeUpTo Q))
    (χ₀ : PrimeCharacterData (schedule k 0) width Q)
    (hχ₀ : ∀ i p, p ∈ E₀ i → χ₀ i p ≠ 1) :
    ∀ i p, p ∈ scheduledPrimeShells k width E₀ j i →
      scheduledCharacterData k width χ₀ j i p ≠ 1 := by
  intro i p hp
  rw [scheduledPrimeShells_eq_origin] at hp
  exact hχ₀ _ p hp

theorem scheduledPrimeShells_source_prime_gt (k j : ℕ) (width : Role → ℕ) {Q U : ℕ}
    (E₀ : (schedule k 0).Constituent width → Finset (PrimeUpTo Q))
    (hU : ∀ i p, p ∈ E₀ i → U < p.val) :
    ∀ i p, p ∈ scheduledPrimeShells k width E₀ j i → U < p.val := by
  intro i p hp
  rw [scheduledPrimeShells_eq_origin] at hp
  exact hU _ p hp

end Ostmann.Characters.Template

end

end OAI
