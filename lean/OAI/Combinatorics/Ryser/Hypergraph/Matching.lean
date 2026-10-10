import OAI.Combinatorics.Ryser.Hypergraph.Definitions

namespace OAI

namespace RyserCoveringCounterexample

variable {V : Type*} [instDecidableEqV : DecidableEq V]

@[simp] theorem mem_matchings {H M : Hypergraph V} :
    M ∈ matchings H ↔ IsMatching H M := let _ := instDecidableEqV; by
  classical
  simp only [matchings, Finset.mem_filter, Finset.mem_powerset, IsMatching]

theorem isMatching_empty (H : Hypergraph V) : IsMatching H ∅ := let _ := instDecidableEqV; by
  constructor
  · exact Finset.empty_subset H
  · simp

theorem isMatching_singleton {H : Hypergraph V} {e : Finset V} (he : e ∈ H) :
    IsMatching H {e} := let _ := instDecidableEqV; by
  constructor
  · exact Finset.singleton_subset_iff.mpr he
  · simp

theorem matchings_nonempty (H : Hypergraph V) : (matchings H).Nonempty :=
  ⟨∅, mem_matchings.mpr (isMatching_empty H)⟩

theorem IsMatching.card_le_matchingNumber {H M : Hypergraph V}
    (hM : IsMatching H M) : M.card ≤ matchingNumber H := by
  exact Finset.le_sup (mem_matchings.mpr hM)

theorem matchingNumber_le_iff {H : Hypergraph V} (n : ℕ) :
    matchingNumber H ≤ n ↔ ∀ M, IsMatching H M → M.card ≤ n := by
  change (matchings H).sup Finset.card ≤ n ↔ _
  rw [Finset.sup_le_iff]
  constructor
  · intro h M hM
    exact h M (mem_matchings.mpr hM)
  · intro h M hM
    exact h M (mem_matchings.mp hM)

theorem matchingNumber_le {H : Hypergraph V} {n : ℕ}
    (h : ∀ M, IsMatching H M → M.card ≤ n) : matchingNumber H ≤ n :=
  (matchingNumber_le_iff n).mpr h

theorem exists_isMatching_card_eq_matchingNumber (H : Hypergraph V) :
    ∃ M, IsMatching H M ∧ M.card = matchingNumber H := by
  obtain ⟨M, hM, hcard⟩ :=
    Finset.exists_mem_eq_sup (matchings H) (matchings_nonempty H) Finset.card
  exact ⟨M, mem_matchings.mp hM, hcard.symm⟩

theorem matchingNumber_le_card (H : Hypergraph V) : matchingNumber H ≤ H.card := by
  apply matchingNumber_le
  intro M hM
  exact Finset.card_le_card hM.1

@[simp] theorem matchingNumber_empty : matchingNumber (∅ : Hypergraph V) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa only [Finset.card_empty] using matchingNumber_le_card (∅ : Hypergraph V)

theorem one_le_matchingNumber_of_nonempty {H : Hypergraph V} (hH : H.Nonempty) :
    1 ≤ matchingNumber H := by
  obtain ⟨e, he⟩ := hH
  simpa only [Finset.card_singleton] using
    (isMatching_singleton he).card_le_matchingNumber

theorem IsMatching.card_le_one_of_intersecting {H M : Hypergraph V}
    (hM : IsMatching H M) (hH : Intersecting H) : M.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hne
  obtain ⟨v, hv⟩ := hH e (hM.1 he) f (hM.1 hf) hne
  exact (Finset.disjoint_left.mp (hM.2 he hf hne))
    (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2

theorem matchingNumber_eq_one_of_nonempty_intersecting {H : Hypergraph V}
    (hH : H.Nonempty) (hI : Intersecting H) : matchingNumber H = 1 := by
  apply le_antisymm
  · apply matchingNumber_le
    intro M hM
    exact hM.card_le_one_of_intersecting hI
  · exact one_le_matchingNumber_of_nonempty hH

end RyserCoveringCounterexample

end OAI
