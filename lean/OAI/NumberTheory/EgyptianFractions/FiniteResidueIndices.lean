import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Natural indices for a finite sample space. Distinct samples remain distinct
indices even when their integer-valued data agree. -/
def residueIndices (α : Type*) [Fintype α] : Finset ℕ :=
  Finset.range (Fintype.card α)

/-- Extend finite sample data by zero outside their canonical natural indices. -/
def residueEntry {α β : Type*} [Fintype α] [Zero β] (f : α → β) (i : ℕ) : β :=
  if hi : i < Fintype.card α then f ((Fintype.equivFin α).symm ⟨i, hi⟩) else 0

@[simp] theorem residueIndices_card (α : Type*) [Fintype α] :
    (residueIndices α).card = Fintype.card α := by
  simp [residueIndices]

@[simp] theorem mem_residueIndices {α : Type*} [Fintype α] {i : ℕ} :
    i ∈ residueIndices α ↔ i < Fintype.card α := by
  simp [residueIndices]

@[simp] theorem residueEntry_equivFin {α β : Type*} [Fintype α] [Zero β]
    (f : α → β) (a : α) :
    residueEntry f (Fintype.equivFin α a).val = f a := by
  simp [residueEntry]

/-- Nonemptiness transfers without any injectivity requirement on the data. -/
@[simp] theorem residueIndices_nonempty_iff (α : Type*) [Fintype α] :
    (residueIndices α).Nonempty ↔ Nonempty α := by
  rw [← Finset.card_pos, residueIndices_card, Fintype.card_pos_iff]

/-- A pointwise assertion can be transported to the numeric indices. -/
theorem forall_residueEntry_iff {α β : Type*} [Fintype α] [Zero β]
    (f : α → β) (P : β → Prop) :
    (∀ i ∈ residueIndices α, P (residueEntry f i)) ↔ ∀ a, P (f a) := by
  constructor
  · intro h a
    simpa using h (Fintype.equivFin α a).val (by simp)
  · intro h i hi
    have hi' : i < Fintype.card α := mem_residueIndices.mp hi
    simpa [residueEntry, hi'] using h ((Fintype.equivFin α).symm ⟨i, hi'⟩)

/-- Full finite sums preserve sample multiplicity under the natural reindexing. -/
theorem sum_residueEntry {α β γ : Type*} [Fintype α] [Zero β]
    [AddCommMonoid γ] (f : α → β) (g : β → γ) :
    (∑ i ∈ residueIndices α, g (residueEntry f i)) = ∑ a, g (f a) := by
  rw [residueIndices, ← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin (Fintype.card α), g (residueEntry f i.val)) =
        ∑ a : α, g (residueEntry f (Fintype.equivFin α a).val) :=
      (Equiv.sum_comp (Fintype.equivFin α) _).symm
    _ = ∑ a : α, g (f a) := by simp

/-- Filtering keeps repeated equal data as distinct samples. -/
theorem card_filter_residueEntry {α β : Type*} [Fintype α] [Zero β]
    (f : α → β) (P : β → Prop) [DecidablePred P] :
    ((residueIndices α).filter (fun i => P (residueEntry f i))).card =
      (Finset.univ.filter (fun a : α => P (f a))).card := by
  classical
  rw [Finset.card_filter, Finset.card_filter]
  exact sum_residueEntry f (fun x => if P x then 1 else 0)

/-- The same sample is used for all components of indexed arithmetic data. -/
theorem forall_residueEntry₂_iff {α β γ : Type*} [Fintype α] [Zero β] [Zero γ]
    (f : α → β) (g : α → γ) (P : β → γ → Prop) :
    (∀ i ∈ residueIndices α, P (residueEntry f i) (residueEntry g i)) ↔
      ∀ a, P (f a) (g a) := by
  constructor
  · intro h a
    simpa using h (Fintype.equivFin α a).val (by simp)
  · intro h i hi
    have hi' : i < Fintype.card α := mem_residueIndices.mp hi
    simpa [residueEntry, hi'] using h ((Fintype.equivFin α).symm ⟨i, hi'⟩)

/-- Function-valued residue or quotient data commute with evaluation. -/
@[simp] theorem residueEntry_apply {α β γ : Type*} [Fintype α] [Zero γ]
    (f : α → β → γ) (i : ℕ) (b : β) :
    residueEntry f i b = residueEntry (fun a => f a b) i := by
  unfold residueEntry
  split <;> rfl

/-- Reindexing does not change the normalized complex Fourier sum, even when
sample data have repeated values or the sample space is empty. -/
theorem normalized_sum_residueEntry {α β : Type*} [Fintype α] [Zero β]
    (f : α → β) (phase : β → ℂ) :
    ((residueIndices α).card : ℂ)⁻¹ *
        (∑ i ∈ residueIndices α, phase (residueEntry f i)) =
      (Fintype.card α : ℂ)⁻¹ * ∑ a, phase (f a) := by
  rw [residueIndices_card, sum_residueEntry]

end Problem337

end

end OAI
