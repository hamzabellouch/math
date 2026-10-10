import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace OAI

/-!
# Exact cycle–clique Ramsey statements

The red edges are the edges of `G`; a blue clique is an independent set
in `G`. The cycle is a non-induced copy on exactly `m` distinct vertices.
For the main theorem all cycle lengths are at least three.
-/

namespace CycleClique.Construction
variable {V W : Type*}

/-- Cyclic successor, defined also for the empty index type. -/
def cycleNext {m : ℕ} (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- An injectively labelled cycle, including its closing edge. -/
def HasCycle (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ f : Fin m → V, Function.Injective f ∧ ∀ i, G.Adj (f i) (f (cycleNext i))

/-- An independent set of exactly `n` vertices. -/
def HasIndependent (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : Fin n → V, Function.Injective f ∧ ∀ i j, ¬ G.Adj (f i) (f j)

/-- The red-cycle/blue-clique property at order `N`. -/
def RamseyProperty (m n N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), HasCycle G m ∨ HasIndependent G n

/-- Specifying the least forcing order avoids an existence convention for `sInf`. -/
def IsRamseyNumber (m n N : ℕ) : Prop :=
  RamseyProperty m n N ∧ ∀ M < N, ¬ RamseyProperty m n M

theorem HasCycle.map {G : SimpleGraph V} {H : SimpleGraph W} {m : ℕ}
    (h : HasCycle G m) (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ {x y}, G.Adj x y → H.Adj (f x) (f y)) : HasCycle H m := by
  obtain ⟨c, hc, he⟩ := h
  exact ⟨f ∘ c, hf.comp hc, fun i => hadj (he i)⟩

theorem HasIndependent.map {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}
    (h : HasIndependent G n) (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ {x y}, H.Adj (f x) (f y) → G.Adj x y) : HasIndependent H n := by
  obtain ⟨c, hc, he⟩ := h
  exact ⟨f ∘ c, hf.comp hc, fun i j h => he i j (hadj h)⟩

theorem HasIndependent.card_le [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (h : HasIndependent G n) : n ≤ Fintype.card V := by
  obtain ⟨f, hf, _⟩ := h
  simpa using Fintype.card_le_of_injective f hf

theorem HasCycle.card_le [Fintype V] {G : SimpleGraph V} {m : ℕ}
    (h : HasCycle G m) : m ≤ Fintype.card V := by
  obtain ⟨f, hf, _⟩ := h
  simpa using Fintype.card_le_of_injective f hf

end CycleClique.Construction

end OAI
