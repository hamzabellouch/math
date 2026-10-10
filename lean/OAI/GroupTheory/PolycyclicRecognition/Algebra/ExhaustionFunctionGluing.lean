import Mathlib.Data.Set.Basic

namespace OAI

/-! # Gluing compatible functions on an increasing countable cover -/

noncomputable section
namespace PolycyclicRecognition

theorem exists_function_of_compatible_exhaustion
    {α β : Type*} (S : ℕ → Set α) (hS : Monotone S)
    (hcover : ∀ a, ∃ n, a ∈ S n) (f : ∀ n, S n → β)
    (hf : ∀ n (a : S n), f (n + 1) ⟨a, hS (Nat.le_succ n) a.property⟩ = f n a) :
    ∃ g : α → β, ∀ n (a : S n), g a = f n a := by
  have hle (n m : ℕ) (hnm : n ≤ m) (a : S n) :
      f m ⟨a, hS hnm a.property⟩ = f n a := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih =>
      exact (hf m ⟨a, hS hnm a.property⟩).trans ih
  let g (a : α) := f (hcover a).choose ⟨a, (hcover a).choose_spec⟩
  refine ⟨g, ?_⟩
  intro n a
  let m := (hcover (a : α)).choose
  let b : S m := ⟨a, (hcover (a : α)).choose_spec⟩
  exact (hle m (max m n) (le_max_left _ _) b).symm.trans
    (hle n (max m n) (le_max_right _ _) a)

end PolycyclicRecognition

end

end OAI
