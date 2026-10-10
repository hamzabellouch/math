import Mathlib.Logic.Equiv.Basic
import OAI.NumberTheory.Ostmann.Construction.ScheduleWordSlots
import OAI.NumberTheory.Ostmann.Construction.FinalReassignments
import OAI.NumberTheory.Ostmann.Construction.ScheduledRolePrior

namespace OAI

/-! # The final parity reassignments as permutations of actual active slots -/

namespace Ostmann
open scoped Classical BigOperators

/-- An actual copied word coordinate belongs to H at every depth. -/
noncomputable def scheduledWordH {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (t : Fin n → Bool) (i : {i : I // role i = .word}) :
    CopyScheduleH role n :=
  ⟨copySchedulePath n t i.val, copyScheduleSurvives_path role i.val i.property n t,
    by rw [copyScheduleRole_path role i.val i.property n t]; rfl⟩

theorem scheduledWordH_injective {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    Function.Injective (fun x : (Fin n → Bool) × {i : I // role i = .word} =>
      scheduledWordH role n x.1 x.2) := by
  intro x y h
  have he : (x.1, x.2.val) = (y.1, y.2.val) :=
    copySchedulePath_injective n (congrArg Subtype.val h)
  exact Prod.ext (congrArg (fun z : (Fin n → Bool) × I => z.1) he)
    (Subtype.ext (congrArg (fun z : (Fin n → Bool) × I => z.2) he))

noncomputable def scheduledWordHEquiv {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    ((Fin n → Bool) × {i : I // role i = .word}) ≃
      {h : CopyScheduleH role n // copyScheduleRole role n h.val = .word} :=
  Equiv.ofBijective (fun x => ⟨scheduledWordH role n x.1 x.2,
    copyScheduleRole_path role x.2.val x.2.property n x.1⟩) (by
      constructor
      · intro x y h
        exact scheduledWordH_injective role n (congrArg Subtype.val h)
      · intro h
        obtain ⟨t, i, hi, he⟩ := surviving_word_is_path role n h.val.val h.val.property.1 h.property
        refine ⟨(t, ⟨i, hi⟩), ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact he.symm)

noncomputable def scheduledParityCoordinates {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word}) :
    (ParityPathSum n × Fin m) ≃
      {h : CopyScheduleH role (n + 1) // copyScheduleRole role (n + 1) h.val = .word} :=
  ((parityPathSumEquiv n).prodCongr word).trans (scheduledWordHEquiv role (n + 1))

/-- Only actual word coordinates are reassigned. Every other H coordinate,
including future pivots and fresh anchors, is fixed. -/
noncomputable def scheduledFinalPerm {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : FinalParityReassignments n m) : Equiv.Perm (CopyScheduleH role (n + 1)) :=
  ((scheduledParityCoordinates role n m word).permCongr (paritySlotPerm e)).subtypeCongr
    (Equiv.refl _)

theorem scheduledFinalPerm_word {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : FinalParityReassignments n m) (x : ParityPathSum n × Fin m) :
    scheduledFinalPerm role n m word e
      (scheduledWordH role (n + 1) (parityPathValue x.1) (word x.2)) =
    scheduledWordH role (n + 1) (parityPathValue (paritySlotPerm e x).1)
      (word (paritySlotPerm e x).2) := by
  have hx : (scheduledParityCoordinates role n m word x).val =
      scheduledWordH role (n + 1) (parityPathValue x.1) (word x.2) := rfl
  rw [← hx]
  unfold scheduledFinalPerm
  rw [Equiv.Perm.subtypeCongr.left_apply_subtype]
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

theorem scheduledFinalPerm_other {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : FinalParityReassignments n m) (h : CopyScheduleH role (n + 1))
    (hh : copyScheduleRole role (n + 1) h.val ≠ .word) :
    scheduledFinalPerm role n m word e h = h := by
  unfold scheduledFinalPerm
  simp only [Equiv.Perm.subtypeCongr.apply, dite_eq_right hh, Equiv.refl_apply]

theorem scheduledFinalPerm_injective {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word}) :
    Function.Injective (scheduledFinalPerm role n m word) := by
  intro e f hef
  apply paritySlotPerm_injective
  apply Equiv.ext
  intro x
  have hx := congrArg (fun g => g (scheduledWordH role (n + 1)
    (parityPathValue x.1) (word x.2))) hef
  rw [scheduledFinalPerm_word, scheduledFinalPerm_word] at hx
  have he : (parityPathValue (paritySlotPerm e x).1, word (paritySlotPerm e x).2) =
      (parityPathValue (paritySlotPerm f x).1, word (paritySlotPerm f x).2) :=
    scheduledWordH_injective role (n + 1) hx
  exact Prod.ext (parityPathValue_injective n (congrArg Prod.fst he))
    (word.injective (congrArg Prod.snd he))

theorem scheduledFinalPerm_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : FinalParityReassignments n m) (h : CopyScheduleH role (n + 1)) :
    copyScheduleOrigin (n + 1) (scheduledFinalPerm role n m word e h).val =
      copyScheduleOrigin (n + 1) h.val := by
  by_cases hw : copyScheduleRole role (n + 1) h.val = .word
  · obtain ⟨x, hx⟩ := (scheduledParityCoordinates role n m word).surjective ⟨h, hw⟩
    have he : scheduledWordH role (n + 1) (parityPathValue x.1) (word x.2) = h :=
      congrArg Subtype.val hx
    rw [← he, scheduledFinalPerm_word]
    simp only [scheduledWordH, copyScheduleOrigin_path, paritySlotPerm_preserves_position]
  · rw [scheduledFinalPerm_other role n m word e h hw]

/-- Each original marginal is preserved, including different marginals for
bulk, top, anchor and pivot roles. -/
theorem scheduledFinalPerm_product_prior {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (e : FinalParityReassignments n m)
    (μ : I → A → ℝ) (x : CopyScheduleH role (n + 1) → A) :
    (∏ h, μ (copyScheduleOrigin (n + 1) h.val)
      (x (scheduledFinalPerm role n m word e h))) =
    ∏ h, μ (copyScheduleOrigin (n + 1) h.val) (x h) := by
  calc
    _ = ∏ h, μ (copyScheduleOrigin (n + 1)
        (scheduledFinalPerm role n m word e h).val)
        (x (scheduledFinalPerm role n m word e h)) := by
      apply Finset.prod_congr rfl
      intro h _
      rw [scheduledFinalPerm_origin]
    _ = _ := Equiv.prod_comp (scheduledFinalPerm role n m word e)
      (fun h => μ (copyScheduleOrigin (n + 1) h.val) (x h))

end Ostmann

end OAI
