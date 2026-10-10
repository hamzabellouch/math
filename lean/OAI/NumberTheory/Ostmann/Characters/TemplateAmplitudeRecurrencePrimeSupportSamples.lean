import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorStates
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSupportBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries

theorem withinAtomPrimeSupport_scheduledSample (k j : ℕ) (hj : j < k)
    (width : Role → ℕ) {Q : ℕ}
    (w : Fin (width ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q) :
    withinAtomPrimeSupport (schedule k j) width (scheduledSample k j hj width w h y) ↔
      Pairwise (fun a b => (w a).val.Coprime (w b).val) ∧
      copiedWithinAtomPrimeSupport (schedule k j) j width h ∧
      outsideWithinAtomPrimeSupport (schedule k j) j width y := by
  constructor
  · intro hs
    constructor
    · simpa only [scheduledSample_pivot] using hs (pivotSlot k j hj).val
    constructor
    · intro i a b hab
      have hh := hs i.val hab
      change (scheduledSample k j hj width w h y
        (copiedConstituentOld (schedule k j) j width ⟨i,a⟩)).val.Coprime
        (scheduledSample k j hj width w h y
          (copiedConstituentOld (schedule k j) j width ⟨i,b⟩)).val at hh
      simpa only [scheduledSample_copied] using hh
    · intro i a b hab
      have hh := hs i.val hab
      change (scheduledSample k j hj width w h y
        (outsideConstituentOld (schedule k j) j width ⟨i,a⟩)).val.Coprime
        (scheduledSample k j hj width w h y
          (outsideConstituentOld (schedule k j) j width ⟨i,b⟩)).val at hh
      simpa only [scheduledSample_outside] using hh
  · rintro ⟨hw,hh,hy⟩ i
    by_cases hp : (schedule k j).IsPivot j i
    · have he : i=(pivotSlot k j hj).val := congrArg Subtype.val
        (pivotSlot_unique k j hj ⟨i,hp⟩)
      subst i
      simpa only [scheduledSample_pivot] using hw
    · by_cases hc : (schedule k j).IsCopied j i
      · change Pairwise (fun a b =>
          (scheduledSample k j hj width w h y
            (copiedConstituentOld (schedule k j) j width ⟨⟨i,hc⟩,a⟩)).val.Coprime
          (scheduledSample k j hj width w h y
            (copiedConstituentOld (schedule k j) j width ⟨⟨i,hc⟩,b⟩)).val)
        simpa only [scheduledSample_copied] using hh ⟨i,hc⟩
      · change Pairwise (fun a b =>
          (scheduledSample k j hj width w h y
            (outsideConstituentOld (schedule k j) j width ⟨⟨i,hp,hc⟩,a⟩)).val.Coprime
          (scheduledSample k j hj width w h y
            (outsideConstituentOld (schedule k j) j width ⟨⟨i,hp,hc⟩,b⟩)).val)
        simpa only [scheduledSample_outside] using hy ⟨i,hp,hc⟩

theorem withinAtomPrimeSupport_nextSample (T : Layout) (j : ℕ)
    (width : Role → ℕ) {Q : ℕ}
    (hL hR : CopiedConstituent T j width → PrimeUpTo Q)
    (y : OutsideConstituent T j width → PrimeUpTo Q) :
    withinAtomPrimeSupport (T.step j) width (nextSample T j width hL hR y) ↔
      copiedWithinAtomPrimeSupport T j width hL ∧
      copiedWithinAtomPrimeSupport T j width hR ∧
      outsideWithinAtomPrimeSupport T j width y := by
  constructor
  · intro hs
    exact ⟨fun i => hs (.inl (i,true)), fun i => hs (.inl (i,false)),
      fun i => hs (.inr i)⟩
  · rintro ⟨hl,hr,hy⟩ (⟨i,b⟩ | i)
    · cases b
      · exact hr i
      · exact hl i
    · exact hy i

theorem scheduledSample_prime_support_iff (k j : ℕ) (hj : j < k)
    (width : Role → ℕ) {Q : ℕ}
    (w : Fin (width ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q) :
    Pairwise (fun a b =>
      (scheduledSample k j hj width w h y a).val.Coprime
      (scheduledSample k j hj width w h y b).val) ↔
      Pairwise (fun a b => IsCoprime
        (sourceState k j (characterTupleProduct w:ℤ)
          (copiedSampleState (schedule k j) j width h)
          (outsideSampleState (schedule k j) j width y) a)
        (sourceState k j (characterTupleProduct w:ℤ)
          (copiedSampleState (schedule k j) j width h)
          (outsideSampleState (schedule k j) j width y) b)) ∧
      Pairwise (fun a b => (w a).val.Coprime (w b).val) ∧
      copiedWithinAtomPrimeSupport (schedule k j) j width h ∧
      outsideWithinAtomPrimeSupport (schedule k j) j width y := by
  rw [constituent_prime_support_iff, constituentSampleState_scheduledSample,
    withinAtomPrimeSupport_scheduledSample]

theorem nextSample_prime_support_iff (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (hL hR : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q) :
    Pairwise (fun a b => (nextSample (schedule k j) j width hL hR y a).val.Coprime
      (nextSample (schedule k j) j width hL hR y b).val) ↔
      Pairwise (fun a b => IsCoprime
        (pairedState k j (copiedSampleState (schedule k j) j width hL)
          (copiedSampleState (schedule k j) j width hR)
          (outsideSampleState (schedule k j) j width y) a)
        (pairedState k j (copiedSampleState (schedule k j) j width hL)
          (copiedSampleState (schedule k j) j width hR)
          (outsideSampleState (schedule k j) j width y) b)) ∧
      copiedWithinAtomPrimeSupport (schedule k j) j width hL ∧
      copiedWithinAtomPrimeSupport (schedule k j) j width hR ∧
      outsideWithinAtomPrimeSupport (schedule k j) j width y := by
  rw [constituent_prime_support_iff]
  rw [constituentSampleState_nextSample]
  rw [withinAtomPrimeSupport_nextSample]

end Ostmann.Characters.Template

end

end OAI
