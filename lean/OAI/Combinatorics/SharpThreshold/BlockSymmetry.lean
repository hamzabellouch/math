import Mathlib

namespace OAI

universe u v w

noncomputable section

namespace Problem313

/-- Assemble a configuration on a coordinate subset and its complement. -/
def pasteCube {α : Type u} {β : Type v} (P : α → Prop) [DecidablePred P]
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) : α → β :=
  fun i => if hi : P i then x ⟨i, hi⟩ else y ⟨i, hi⟩

@[simp]
theorem pasteCube_of_pos {α : Type u} {β : Type v} (P : α → Prop) [DecidablePred P]
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) (i : α) (hi : P i) :
    pasteCube P x y i = x ⟨i, hi⟩ := by
  simp [pasteCube, hi]

@[simp]
theorem pasteCube_of_neg {α : Type u} {β : Type v} (P : α → Prop) [DecidablePred P]
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) (i : α) (hi : ¬ P i) :
    pasteCube P x y i = y ⟨i, hi⟩ := by
  simp [pasteCube, hi]

/-- A permutation preserving the free coordinates and fixing all exterior coordinates
commutes with pasting, without changing the fixed exterior configuration. -/
theorem pasteCube_reindex {α : Type u} {β : Type v} (P : α → Prop) [DecidablePred P]
    (π : Equiv.Perm α) (hP : ∀ i, P i ↔ P (π i))
    (hfix : ∀ i, ¬ P i → π i = i)
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) :
    (fun i => pasteCube P x y (π.symm i)) =
      pasteCube P (fun i => x ((π.subtypeEquiv hP).symm i)) y := by
  funext i
  by_cases hi : P i
  · have hi' : P (π.symm i) := (hP _).mpr (by simpa using hi)
    simp only [pasteCube, dite_eq_left hi, dite_eq_left hi']
    rfl
  · have hsi : π.symm i = i := (π.symm_apply_eq).mpr (hfix i hi).symm
    simp [pasteCube, hi, hsi]

/-- Restriction of a function to a coordinate subset, with exterior values fixed. -/
def restrictCube {α : Type u} {β : Type v} {γ : Type w} (P : α → Prop) [DecidablePred P]
    (f : (α → β) → γ) (y : {i // ¬ P i} → β) : ({i // P i} → β) → γ :=
  fun x => f (pasteCube P x y)

/-- Coordinate symmetry survives conditioning outside a set when the symmetry
fixes every exterior coordinate individually. -/
theorem restrictCube_invariant {α : Type u} {β : Type v} {γ : Type w} (P : α → Prop) [DecidablePred P]
    (π : Equiv.Perm α) (hP : ∀ i, P i ↔ P (π i))
    (hfix : ∀ i, ¬ P i → π i = i) (f : (α → β) → γ)
    (hf : ∀ z, f (fun i => z (π.symm i)) = f z)
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) :
    restrictCube P f y (fun i => x ((π.subtypeEquiv hP).symm i)) =
      restrictCube P f y x := by
  unfold restrictCube
  rw [← pasteCube_reindex P π hP hfix x y]
  exact hf _

end Problem313

end

end OAI
