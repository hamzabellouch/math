import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorDisintegration

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

@[simp] theorem scheduledSample_pivot (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (w : Fin (width ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (a : Fin (width ((schedule k j).role (pivotSlot k j hj).val))) :
    scheduledSample k j hj width w h y ⟨(pivotSlot k j hj).val,a⟩ = w a := by
  change assemblePriorSample (scheduledConstituentInput k j hj width) w h y
    (scheduledConstituentInput k j hj width (.inl a)) = _
  simp only [assemblePriorSample,Equiv.symm_apply_apply,Sum.elim_inl]

@[simp] theorem scheduledSample_copied (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (w : Fin (width ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (i : CopiedConstituent (schedule k j) j width) :
    scheduledSample k j hj width w h y (copiedConstituentOld (schedule k j) j width i) = h i := by
  change assemblePriorSample (scheduledConstituentInput k j hj width) w h y
    (scheduledConstituentInput k j hj width (.inr (.inl i))) = _
  simp only [assemblePriorSample,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]

@[simp] theorem scheduledSample_outside (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (w : Fin (width ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (i : OutsideConstituent (schedule k j) j width) :
    scheduledSample k j hj width w h y (outsideConstituentOld (schedule k j) j width i) = y i := by
  change assemblePriorSample (scheduledConstituentInput k j hj width) w h y
    (scheduledConstituentInput k j hj width (.inr (.inr i))) = _
  simp only [assemblePriorSample,Equiv.symm_apply_apply,Sum.elim_inr]

theorem constituentSampleState_pos (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (x : T.Constituent width → PrimeUpTo Q) (i : T.Slot) :
    0 < constituentSampleState T width x i := by
  apply Finset.prod_pos
  intro a ha
  exact_mod_cast (primeUpTo_prime (x ⟨i,a⟩)).pos

theorem constituentSampleState_scheduledSample (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (w : Fin (width ((schedule k j).role (pivotSlot k j hj).val)) → PrimeUpTo Q)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q) :
    constituentSampleState (schedule k j) width (scheduledSample k j hj width w h y) =
      sourceState k j (characterTupleProduct w:ℤ)
        (copiedSampleState (schedule k j) j width h) (outsideSampleState (schedule k j) j width y) := by
  funext i
  unfold sourceState
  by_cases hp : (schedule k j).IsPivot j i
  · have he : i=(pivotSlot k j hj).val := congrArg Subtype.val (pivotSlot_unique k j hj ⟨i,hp⟩)
    subst i
    rw [childState_pivot _ _ _ _ _ _ (pivotSlot k j hj).property]
    simp only [constituentSampleState,scheduledSample_pivot,characterTupleProduct,Nat.cast_prod]
  · by_cases hc : (schedule k j).IsCopied j i
    · rw [childState_copied _ _ _ _ _ ⟨i,hc⟩]
      change (∏ a : Fin (width ((schedule k j).role i)),
        ((scheduledSample k j hj width w h y ⟨i,a⟩).val:ℤ)) =
        ∏ a : Fin (width ((schedule k j).role i)), ((h ⟨⟨i,hc⟩,a⟩).val:ℤ)
      apply Finset.prod_congr rfl
      intro a ha
      exact congrArg (fun p : PrimeUpTo Q => (p.val:ℤ))
        (scheduledSample_copied k j hj width w h y ⟨⟨i,hc⟩,a⟩)
    · rw [childState_outside _ _ _ _ _ ⟨i,hp,hc⟩]
      change (∏ a : Fin (width ((schedule k j).role i)),
        ((scheduledSample k j hj width w h y ⟨i,a⟩).val:ℤ)) =
        ∏ a : Fin (width ((schedule k j).role i)), ((y ⟨⟨i,hp,hc⟩,a⟩).val:ℤ)
      apply Finset.prod_congr rfl
      intro a ha
      exact congrArg (fun p : PrimeUpTo Q => (p.val:ℤ))
        (scheduledSample_outside k j hj width w h y ⟨⟨i,hp,hc⟩,a⟩)

theorem constituentSampleState_nextSample (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (hL hR : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q) :
    constituentSampleState (schedule k (j+1)) width (nextSample (schedule k j) j width hL hR y) =
      pairedState k j (copiedSampleState (schedule k j) j width hL)
        (copiedSampleState (schedule k j) j width hR) (outsideSampleState (schedule k j) j width y) := by
  funext i
  rcases i with ⟨i,b⟩ | i
  · cases b <;> rfl
  · rfl

end Ostmann.Characters.Template

end

end OAI
