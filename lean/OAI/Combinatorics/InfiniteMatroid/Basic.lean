import Mathlib

namespace OAI

open Set Matroid

namespace InfiniteMatroidCounterexample

abbrev D := (m : ℕ) × ((Fin m → Bool) → Bool)
abbrev E0 := D × Bool
abbrev E := ℤ × D

def contractOnto {α : Type*} (M : Matroid α) (C : Set α) : Matroid α :=
  (M.dual ↾ C).dual

def HasPackingCovering {α : Type*} (M₀ M₁ : Matroid α) : Prop :=
  ∃ P C S₀ S₁ I₀ I₁ : Set α,
    Disjoint P C ∧ P ∪ C = M₀.E ∧ M₁.E = M₀.E ∧
    S₀ ⊆ P ∧ S₁ ⊆ P ∧ Disjoint S₀ S₁ ∧
    (M₀ ↾ P).Spanning S₀ ∧ (M₁ ↾ P).Spanning S₁ ∧
    I₀ ⊆ C ∧ I₁ ⊆ C ∧
    (contractOnto M₀ C).Indep I₀ ∧
    (contractOnto M₁ C).Indep I₁ ∧ I₀ ∪ I₁ = C

end InfiniteMatroidCounterexample

end OAI
