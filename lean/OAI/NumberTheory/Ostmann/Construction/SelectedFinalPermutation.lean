import OAI.NumberTheory.Ostmann.Construction.SelectedBulkCoordinates

namespace OAI

/-! # Final parity permutations fix every top slot

Only the explicitly selected bulk slots are permuted among paths of equal
parity. The remaining word slots, in particular the top labels, stay fixed.
-/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedParityH {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    (ParityPathSum n × Fin m) ↪ CopyScheduleH role (n + 1) where
  toFun x := scheduledWordH role (n + 1) (parityPathValue x.1) ⟨bulk x.2, hbulk x.2⟩
  inj' := by
    intro x y h
    have he := @copySchedulePath_injective I (n + 1)
      (parityPathValue x.1, bulk x.2) (parityPathValue y.1, bulk y.2)
      (congrArg Subtype.val h)
    exact Prod.ext (parityPathValue_injective n (congrArg Prod.fst he))
      (bulk.injective (congrArg Prod.snd he))

noncomputable def selectedParityCoordinates {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    (ParityPathSum n × Fin m) ≃
      {h : CopyScheduleH role (n + 1) // h ∈ Set.range (selectedParityH role n m bulk hbulk)} :=
  Equiv.ofInjective _ (selectedParityH role n m bulk hbulk).injective

noncomputable def selectedFinalPerm {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) : Equiv.Perm (CopyScheduleH role (n + 1)) :=
  ((selectedParityCoordinates role n m bulk hbulk).permCongr (paritySlotPerm e)).subtypeCongr
    (Equiv.refl _)

theorem selectedFinalPerm_bulk {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) (x : ParityPathSum n × Fin m) :
    selectedFinalPerm role n m bulk hbulk e (selectedParityH role n m bulk hbulk x) =
      selectedParityH role n m bulk hbulk (paritySlotPerm e x) := by
  have hx : (selectedParityCoordinates role n m bulk hbulk x).val =
      selectedParityH role n m bulk hbulk x := rfl
  rw [← hx]
  unfold selectedFinalPerm
  rw [Equiv.Perm.subtypeCongr.left_apply_subtype]
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

theorem selectedFinalPerm_other {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) (h : CopyScheduleH role (n + 1))
    (hh : h ∉ Set.range (selectedParityH role n m bulk hbulk)) :
    selectedFinalPerm role n m bulk hbulk e h = h := by
  unfold selectedFinalPerm
  simp only [Equiv.Perm.subtypeCongr.apply, dite_eq_right hh, Equiv.refl_apply]

@[simp] theorem selectedParityH_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (x : ParityPathSum n × Fin m) :
    copyScheduleOrigin (n + 1) (selectedParityH role n m bulk hbulk x).val = bulk x.2 :=
  copyScheduleOrigin_path (n + 1) _ _

theorem selectedFinalPerm_fixed_of_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) (h : CopyScheduleH role (n + 1))
    (hh : copyScheduleOrigin (n + 1) h.val ∉ Set.range bulk) :
    selectedFinalPerm role n m bulk hbulk e h = h := by
  apply selectedFinalPerm_other
  rintro ⟨x, hx⟩
  apply hh
  refine ⟨x.2, ?_⟩
  have ho := congrArg (fun h : CopyScheduleH role (n + 1) => copyScheduleOrigin (n + 1) h.val) hx
  simpa only [selectedParityH_origin] using ho

theorem selectedFinalPerm_injective {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    Function.Injective (selectedFinalPerm role n m bulk hbulk) := by
  intro e f hef
  apply paritySlotPerm_injective
  apply Equiv.ext
  intro x
  apply (selectedParityH role n m bulk hbulk).injective
  have hx := congrArg (fun g => g (selectedParityH role n m bulk hbulk x)) hef
  simpa only [selectedFinalPerm_bulk] using hx

theorem selectedFinalPerm_origin {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : FinalParityReassignments n m) (h : CopyScheduleH role (n + 1)) :
    copyScheduleOrigin (n + 1) (selectedFinalPerm role n m bulk hbulk e h).val =
      copyScheduleOrigin (n + 1) h.val := by
  by_cases hh : h ∈ Set.range (selectedParityH role n m bulk hbulk)
  · obtain ⟨x, rfl⟩ := hh
    rw [selectedFinalPerm_bulk]
    change copyScheduleOrigin (n + 1) (copySchedulePath (n + 1)
      (parityPathValue (paritySlotPerm e x).1) (bulk (paritySlotPerm e x).2)) =
      copyScheduleOrigin (n + 1) (copySchedulePath (n + 1) (parityPathValue x.1) (bulk x.2))
    simp only [copyScheduleOrigin_path, paritySlotPerm_preserves_position]
  · rw [selectedFinalPerm_other role n m bulk hbulk e h hh]

theorem selectedFinalPerm_product_prior {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) (e : FinalParityReassignments n m)
    (μ : I → A → ℝ) (x : CopyScheduleH role (n + 1) → A) :
    (∏ h, μ (copyScheduleOrigin (n + 1) h.val)
      (x (selectedFinalPerm role n m bulk hbulk e h))) =
    ∏ h, μ (copyScheduleOrigin (n + 1) h.val) (x h) := by
  calc
    _ = ∏ h, μ (copyScheduleOrigin (n + 1)
        (selectedFinalPerm role n m bulk hbulk e h).val)
        (x (selectedFinalPerm role n m bulk hbulk e h)) := by
      apply Finset.prod_congr rfl
      intro h _
      rw [selectedFinalPerm_origin]
    _ = _ := Equiv.prod_comp (selectedFinalPerm role n m bulk hbulk e)
      (fun h => μ (copyScheduleOrigin (n + 1) h.val) (x h))

end Ostmann

end OAI
