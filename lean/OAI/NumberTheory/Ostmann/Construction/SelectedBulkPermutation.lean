import OAI.NumberTheory.Ostmann.Construction.SelectedPrimeFubini
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSymmetrization
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkData
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPermutedProduct

namespace OAI

/-! # Permuting only the selected bulk coordinates in the original law -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedBulkPerm {B J : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) : Equiv.Perm B :=
  (selectedIndexEquiv slot).symm.trans
    ((e.sumCongr (Equiv.refl _)).trans (selectedIndexEquiv slot))

@[simp] theorem selectedBulkPerm_bulk {B J : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) (j : J) : selectedBulkPerm slot e (slot j) = slot (e j) := by
  change selectedIndexEquiv slot ((e.sumCongr (Equiv.refl _))
    ((selectedIndexEquiv slot).symm (selectedIndexEquiv slot (.inl j)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem selectedBulkPerm_nonbulk {B J : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) (i : B) (hi : i ∉ Set.range slot) :
    selectedBulkPerm slot e i = i := by
  change selectedIndexEquiv slot ((e.sumCongr (Equiv.refl _))
    ((selectedIndexEquiv slot).symm (selectedIndexEquiv slot (.inr ⟨i, hi⟩)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem selectedBulkPerm_symm {B J : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) : (selectedBulkPerm slot e).symm = selectedBulkPerm slot e.symm := by
  ext i
  obtain ⟨j, rfl⟩ := (selectedIndexEquiv slot).surjective i
  cases j <;> simp [selectedBulkPerm]

@[simp] theorem selectedBulkPerm_one {B J : Type*} (slot : J ↪ B) :
    selectedBulkPerm slot 1 = 1 := by
  ext i
  simp [selectedBulkPerm]

@[simp] theorem selectedBulkPerm_mul {B J : Type*} (slot : J ↪ B)
    (e f : Equiv.Perm J) : selectedBulkPerm slot (e * f) =
      selectedBulkPerm slot e * selectedBulkPerm slot f := by
  ext i
  obtain ⟨j, rfl⟩ := (selectedIndexEquiv slot).surjective i
  cases j <;> simp [selectedBulkPerm, Equiv.Perm.mul_apply]

noncomputable def selectedBulkSample {B J A : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) (y : B → A) : B → A := y ∘ (selectedBulkPerm slot e).symm

@[simp] theorem selectedBulkSample_bulk {B J A : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) (y : B → A) (j : J) :
    selectedBulkSample slot e y (slot j) = y (slot (e.symm j)) := by
  simp [selectedBulkSample]

@[simp] theorem selectedBulkSample_nonbulk {B J A : Type*} (slot : J ↪ B)
    (e : Equiv.Perm J) (y : B → A) (i : B) (hi : i ∉ Set.range slot) :
    selectedBulkSample slot e y i = y i := by
  simp [selectedBulkSample, hi]

@[simp] theorem selectedBulkSample_one {B J A : Type*} (slot : J ↪ B) (y : B → A) :
    selectedBulkSample slot 1 y = y := by
  simp only [selectedBulkSample, selectedBulkPerm_one]
  rfl

theorem selectedBulkSample_mul {B J A : Type*} (slot : J ↪ B)
    (e f : Equiv.Perm J) (y : B → A) :
    selectedBulkSample slot (e * f) y = selectedBulkSample slot e (selectedBulkSample slot f y) := by
  simp only [selectedBulkSample, selectedBulkPerm_mul]
  rfl

/-- Only the selected coordinates need identical distributions. -/
theorem selectedBulkSample_prior {B J A : Type*} [Fintype B]
    (slot : J ↪ B) (e : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k)) (y : B → A) :
    (∏ i, ν i (selectedBulkSample slot e y i)) = ∏ i, ν i (y i) := by
  have hpres (i : B) : ν i = ν ((selectedBulkPerm slot e).symm i) := by
    obtain ⟨j, rfl⟩ := (selectedIndexEquiv slot).surjective i
    cases j with
    | inl j => simpa using hν j (e.symm j)
    | inr i => simp [i.property]
  calc
    _ = ∏ i, ν ((selectedBulkPerm slot e).symm i)
        (y ((selectedBulkPerm slot e).symm i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [hpres i]
      rfl
    _ = _ := (selectedBulkPerm slot e).symm.prod_comp (fun i => ν i (y i))

theorem selectedBulkSample_sum {B J A : Type*} [Fintype B] [Fintype A]
    (slot : J ↪ B) (e : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k)) (F : (B → A) → ℂ) :
    (∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * F (selectedBulkSample slot e y)) =
      ∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * F y := by
  have h := (bulkArrayEquiv (A := A) (selectedBulkPerm slot e)).sum_comp
    (fun y => ((∏ i, ν i (y i) : ℝ) : ℂ) * F y)
  change (∑ y, ((∏ i, ν i (selectedBulkSample slot e y i) : ℝ) : ℂ) *
    F (selectedBulkSample slot e y)) = _ at h
  simpa only [selectedBulkSample_prior slot e ν hν] using h

theorem selectedBulkSample_bulk_leaves {B A : Type*} (n m : ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (y : B → A) :
    treeLeafMap (List.map (selectedBulkSample slot e y)) n (bulkSlotLeaves n m slot) =
      treeLeafMap (List.map y) n (bulkSlotLeaves n m (slot ∘ e.symm)) := by
  simp only [bulkSlotLeaves_map]
  congr 1
  funext j
  exact selectedBulkSample_bulk slot e y j

theorem treeLeafMap_congr_on_slots {B A : Type*} (n : ℕ)
    (small : TreeLeafTuple (List B) n) (x y : B → A)
    (h : ∀ i ∈ flattenMovingSlots n small, x i = y i) :
    treeLeafMap (List.map x) n small = treeLeafMap (List.map y) n small := by
  induction n with
  | zero => exact List.map_congr_left h
  | succ n ih =>
    apply Prod.ext
    · exact ih small.1 (fun i hi => h i (List.mem_append_left _ hi))
    · exact ih small.2 (fun i hi => h i (List.mem_append_right _ hi))

theorem selectedBulkSample_small_leaves {B J A : Type*} (n : ℕ)
    (small : TreeLeafTuple (List B) n) (slot : J ↪ B) (e : Equiv.Perm J) (y : B → A)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot) :
    treeLeafMap (List.map (selectedBulkSample slot e y)) n small =
      treeLeafMap (List.map y) n small :=
  treeLeafMap_congr_on_slots n small _ _ (fun i hi => selectedBulkSample_nonbulk slot e y i (hsmall i hi))

end Ostmann

end OAI
