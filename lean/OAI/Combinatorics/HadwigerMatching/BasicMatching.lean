import OAI.Combinatorics.HadwigerMatching.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

namespace HadwigerMatching

open scoped BigOperators

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- The empty family is a touching matching. -/
theorem isTouchingMatching_empty (G : SimpleGraph V) :
    IsTouchingMatching G ∅ := by
  simp [IsTouchingMatching]

/-- Every member contributes exactly two vertices. -/
theorem IsTouchingMatching.sum_card_eq {M : Finset (Finset V)}
    (hM : IsTouchingMatching G M) :
    (∑ e ∈ M, e.card) = 2 * M.card := by
  rw [Finset.sum_const_nat (fun e he => (hM.1 e he).1)]
  exact Nat.mul_comm M.card 2

/-- Disjointness bounds twice the number of matching edges by the graph order. -/
theorem IsTouchingMatching.two_mul_card_le [Fintype V]
    {M : Finset (Finset V)} (hM : IsTouchingMatching G M) :
    2 * M.card ≤ Fintype.card V := by
  classical
  have hd : (M : Set (Finset V)).PairwiseDisjoint (fun e => e) := by
    intro e he f hf hne
    exact hM.2.1 e he f hf hne
  have hc : (M.biUnion (fun e => e)).card = 2 * M.card := by
    rw [Finset.card_biUnion hd]
    exact hM.sum_card_eq
  rw [← hc]
  exact Finset.card_le_univ _

/-- Touching matching cardinalities are bounded on a finite vertex type. -/
theorem connectedMatchingNumber_bddAbove [Fintype V] (G : SimpleGraph V) :
    BddAbove {n : ℕ | ∃ M : Finset (Finset V),
      IsTouchingMatching G M ∧ M.card = n} := by
  refine ⟨Fintype.card V, ?_⟩
  rintro n ⟨M, hM, rfl⟩
  have h : M.card + M.card ≤ Fintype.card V := by
    simpa only [two_mul] using hM.two_mul_card_le
  exact (Nat.le_add_right M.card M.card).trans h

/-- Every touching matching is bounded by the connected matching number. -/
theorem matching_card_le_number [Fintype V] {M : Finset (Finset V)}
    (hM : IsTouchingMatching G M) : M.card ≤ connectedMatchingNumber G := by
  exact le_csSup (connectedMatchingNumber_bddAbove G) ⟨M, hM, rfl⟩

/-- The connected matching number is realized by a touching matching. -/
theorem exists_matching_card_eq_number [Fintype V] (G : SimpleGraph V) :
    ∃ M : Finset (Finset V), IsTouchingMatching G M ∧
      M.card = connectedMatchingNumber G := by
  have hne : Set.Nonempty {n : ℕ | ∃ M : Finset (Finset V),
      IsTouchingMatching G M ∧ M.card = n} :=
    ⟨0, ∅, isTouchingMatching_empty G, rfl⟩
  exact Nat.sSup_mem hne (connectedMatchingNumber_bddAbove G)

end HadwigerMatching

end OAI
