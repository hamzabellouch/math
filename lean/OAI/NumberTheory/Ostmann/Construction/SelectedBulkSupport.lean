import OAI.NumberTheory.Ostmann.Characters.MixedBulkSymmetrization
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplatePrior

namespace OAI

/-! # Nonzero bulk averages inherit the original support of one assignment -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedBulkSymmetrize_ne_zero {B A : Type*} (n m : ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (s : ℤ) (y : B → A) (x z : ℝ)
    (h : mixedBulkSymmetrize n m slot F s y x z ≠ 0) :
    ∃ e : Equiv.Perm (TreeLeafIndex n × Fin m), F s (selectedBulkSample slot e y) x z ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  simp only [mixedBulkSymmetrize, finiteFamilyAverage, hn, Finset.sum_const_zero, mul_zero]

theorem selectedBulkSample_injective_iff {B J A C : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) (value : A → C) (y : B → A) :
    Function.Injective (value ∘ selectedBulkSample slot e y) ↔ Function.Injective (value ∘ y) := by
  let E := selectedBulkPerm slot e
  constructor
  · intro h i j hij
    apply E.injective
    apply h
    simpa only [Function.comp_apply, selectedBulkSample, E, Equiv.symm_apply_apply] using hij
  · intro h i j hij
    exact E.symm.injective (h hij)

theorem selectedBulkSample_template_small {A : Type*} (n r m : ℕ)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (y : MovingRegularSlot n r m → A)
    (j : TreeLeafIndex n × Fin r) :
    selectedBulkSample (movingTemplateBulk n r m) e y (j.1, .inl j.2) = y (j.1, .inl j.2) := by
  apply selectedBulkSample_nonbulk
  rintro ⟨i, hi⟩
  have he := congrArg (fun a : MovingRegularSlot n r m => a.2) hi
  cases he

theorem movingRestoreSample_bulk_action {A : Type*} (n r m : ℕ)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) :
    selectedBulkSample (movingTemplateBulk n (4 + r) m) e (movingRestoreSample n r m u y) =
      movingRestoreSample n r m u (selectedBulkSample (movingTemplateBulk n r m) e y) := by
  funext i
  obtain ⟨j, a⟩ := i
  cases a with
  | inl a =>
    refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · calc
        _ = movingRestoreSample n r m u y (j, .inl (a.castAdd r)) :=
          selectedBulkSample_template_small n (4 + r) m e _ (j, a.castAdd r)
        _ = u (j, a) := movingRestoreSample_compensation n r m u y (j, a)
        _ = _ := (movingRestoreSample_compensation n r m u
          (selectedBulkSample (movingTemplateBulk n r m) e y) (j, a)).symm
    · calc
        _ = movingRestoreSample n r m u y (j, .inl (a.natAdd 4)) :=
          selectedBulkSample_template_small n (4 + r) m e _ (j, a.natAdd 4)
        _ = y (j, .inl a) := movingRestoreSample_small n r m u y j a
        _ = selectedBulkSample (movingTemplateBulk n r m) e y (j, .inl a) :=
          (selectedBulkSample_template_small n r m e y (j, a)).symm
        _ = _ := (movingRestoreSample_small n r m u
          (selectedBulkSample (movingTemplateBulk n r m) e y) j a).symm
  | inr a =>
    change selectedBulkSample (movingTemplateBulk n (4 + r) m) e (movingRestoreSample n r m u y)
      (movingTemplateBulk n (4 + r) m (j, a)) =
      movingRestoreSample n r m u (selectedBulkSample (movingTemplateBulk n r m) e y)
        (movingTemplateBulk n (4 + r) m (j, a))
    rw [selectedBulkSample_bulk, movingRestoreSample_bulk, movingRestoreSample_bulk,
      selectedBulkSample_bulk]

end Ostmann

end OAI
