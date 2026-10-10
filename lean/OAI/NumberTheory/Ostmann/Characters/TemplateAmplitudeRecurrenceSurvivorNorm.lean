import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSizeFrequency
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSurvivorNormBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitSource

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem norm_sampledPivotSurviving_le (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (P : ℕ+) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (hχ : ∀ i, χ (scheduledConstituentInput k j hj width (.inr i)) (Sum.elim h y i) ≠ 1)
    (ht : ∀ i, HistoryFrequencyUnits (Sum.elim h y i).val j s t) :
    ‖sampledPivotSurviving k j hj width χ a h y P s t‖ ≤ 1 := by
  let z := Sum.elim h y
  let : ∀ i, Fact (z i).val.Prime := fun i => ⟨primeUpTo_prime (z i)⟩
  exact norm_actualPivotSurviving_le k j hj width _ _ hχ _ _ _ _ ht

theorem norm_sampledRetainedPhase_le (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (P : ℕ+) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (hχ : ∀ i, χ (scheduledConstituentInput k j hj width (.inr i)) (Sum.elim h y i) ≠ 1)
    (ht : ∀ i, HistoryFrequencyUnits (Sum.elim h y i).val j s t) :
    ‖sampledRetainedPhase k j hj width χ a h y P s t‖ ≤ 1 := by
  unfold sampledRetainedPhase
  split_ifs
  · exact norm_sampledPivotSurviving_le k j hj width χ a h y P s t hχ ht
  · simp only [norm_zero, zero_le_one]

theorem norm_unitRetainedPhase_le_of_mass (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q U : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i))
    (ζ : PrimeUnitData (schedule k j) width Q) (hζ : ∀ i p, ‖ζ i p‖ = 1)
    (χ : PrimeCharacterData (schedule k j) width Q) (hχ : ∀ i p, p ∈ E i → χ i p ≠ 1)
    (a : PrimeTranslationData (schedule k j) width Q)
    (hU : ∀ i p, p ∈ E i → U < p.val)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (hh : (copiedPrimePrior (schedule k j) j width E hE).mass h ≠ 0)
    (hy : (outsidePrimePrior (schedule k j) j width E hE).mass y ≠ 0)
    (S : List Bool → Finset ℤ)
    (hS : ∀ path f, f ∈ S path → f ≠ 0 ∧ f.natAbs ≤ U)
    (path : List Bool) (z : SupportedHistory S j path) (P : ℕ+) :
    ‖unitRetainedPhase k j hj width ζ χ a h y P z.val.1 z.val.2‖ ≤ 1 := by
  rw [unitRetainedPhase, norm_mul, norm_survivorUnitMultiplier _ _ _ ζ hζ, one_mul]
  apply norm_sampledRetainedPhase_le
  · intro i
    cases i with
    | inl i =>
      apply hχ
      exact primeProductPrior_mem_of_mass_ne_zero
        (fun i => E (copiedConstituentOld (schedule k j) j width i))
        (fun i => hE (copiedConstituentOld (schedule k j) j width i)) h hh i
    | inr i =>
      apply hχ
      exact primeProductPrior_mem_of_mass_ne_zero
        (fun i => E (outsideConstituentOld (schedule k j) j width i))
        (fun i => hE (outsideConstituentOld (schedule k j) j width i)) y hy i
  · intro i
    cases i with
    | inl i => exact copiedPrimePrior_historyFrequencyUnits _ _ _ E hE hU h hh S hS path z i
    | inr i => exact outsidePrimePrior_historyFrequencyUnits _ _ _ E hE hU y hy S hS path z i

end Ostmann.Characters.Template

end

end OAI
