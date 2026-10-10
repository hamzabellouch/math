import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateEnumeration
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalDiagonalPatterns

namespace OAI

/-! # Identifying arithmetic pattern slots with the full regular template -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPatternTemplateSlots_eq {C : Type*} {N : ℕ} (n r m : ℕ)
    (e : Fin (N + 1) ≃ MovingRegularSlot n r m ⊕ C) :
    movingPatternRegularSlots e n m (movingTemplateSmall n r m) (movingTemplateBulk n r m) =
      (movingTemplateSlotList n r m).map (fun b => e.symm (.inl b)) := by
  exact movingPatternRegularSlots_eq_map e _ _

noncomputable def movingPatternTemplateEquiv {C : Type*} {N : ℕ} (n r m : ℕ)
    (e : Fin (N + 1) ≃ MovingRegularSlot n r m ⊕ C) :
    Fin (movingPatternRegularSlots e n m (movingTemplateSmall n r m)
      (movingTemplateBulk n r m)).length ≃ MovingRegularSlot n r m :=
  (finCongr (by rw [movingPatternTemplateSlots_eq, List.length_map])).trans
    (movingTemplateListEquiv n r m)

theorem movingPatternTemplateEquiv_label {C : Type*} {N : ℕ} (n r m : ℕ)
    (e : Fin (N + 1) ≃ MovingRegularSlot n r m ⊕ C)
    (i : Fin (movingPatternRegularSlots e n m (movingTemplateSmall n r m)
      (movingTemplateBulk n r m)).length) :
    (movingPatternRegularSlots e n m (movingTemplateSmall n r m)
      (movingTemplateBulk n r m)).get i = e.symm (.inl (movingPatternTemplateEquiv n r m e i)) := by
  simp only [movingPatternTemplateEquiv, Equiv.trans_apply, movingTemplateListEquiv_apply,
    List.get_eq_getElem, movingPatternTemplateSlots_eq, List.getElem_map, finCongr_apply,
    Fin.val_cast]

/-- The inactive-slot condition used by the arithmetic theorem follows from
activity of the actual bulk slots. -/
theorem movingPatternTemplate_inactive_not_bulk {C : Type*} {N : ℕ} (n r m : ℕ)
    (e : Fin (N + 1) ≃ MovingRegularSlot n r m ⊕ C)
    (active : MovingRegularSlot n r m → Bool)
    (hactive : ∀ j, active (movingTemplateBulk n r m j) = true)
    (i : Fin (movingPatternRegularSlots e n m (movingTemplateSmall n r m)
      (movingTemplateBulk n r m)).length)
    (hi : active (movingPatternTemplateEquiv n r m e i) = false) :
    (movingPatternRegularSlots e n m (movingTemplateSmall n r m)
      (movingTemplateBulk n r m)).get i ∉
      Set.range (movingPatternBulkEmbedding e (movingTemplateBulk n r m)) := by
  rintro ⟨j, hj⟩
  rw [movingPatternTemplateEquiv_label] at hj
  have he : movingTemplateBulk n r m j = movingPatternTemplateEquiv n r m e i := by
    apply Sum.inl.inj
    apply e.symm.injective
    exact hj
  rw [← he, hactive j] at hi
  cases hi

end Ostmann

end OAI
