import Mathlib

namespace OAI

namespace Balanced
open scoped _root_.Balanced

structure PartiteHypergraph (r n : ℕ) where
  edges : Finset (Fin r → Fin n)

namespace PartiteHypergraph

variable {r n : ℕ}

abbrev Vertex (r n : ℕ) := Fin r × Fin n

def Covers (H : PartiteHypergraph r n) (C : Finset (Vertex r n)) : Prop :=
  ∀ e ∈ H.edges, ∃ i, (i, e i) ∈ C

def Intersecting (H : PartiteHypergraph r n) : Prop :=
  H.edges.Nonempty ∧ ∀ e ∈ H.edges, ∀ f ∈ H.edges, ∃ i, e i = f i

def Nonisolated (H : PartiteHypergraph r n) : Prop :=
  ∀ i v, ∃ e ∈ H.edges, e i = v

def HasCoverNumber (H : PartiteHypergraph r n) (k : ℕ) : Prop :=
  (∃ C : Finset (Vertex r n), H.Covers C ∧ C.card = k) ∧
    ∀ C : Finset (Vertex r n), H.Covers C → k ≤ C.card

end PartiteHypergraph

def BalancedCounterexample (q : ℕ) : Prop :=
  ∃ H : PartiteHypergraph (q + 1) (q + 1),
    H.Intersecting ∧ H.Nonisolated ∧ H.HasCoverNumber (q + 1)

def MainResult : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → q.Prime → BalancedCounterexample q

theorem main_result : MainResult := by
  sorry

end Balanced

end OAI
