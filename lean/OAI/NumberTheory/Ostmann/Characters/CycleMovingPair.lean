import OAI.NumberTheory.Ostmann.Characters.CycleQuartets

namespace OAI

/-! # The two moving leaves in each affected quartet -/

namespace Ostmann

open scoped BigOperators

theorem balanced_two_support_pair {I : Type*} [DecidableEq I]
    (s : Finset I) (sign : I → ℤ) (hsum : ∑ i ∈ s, sign i = 0)
    (hcard : (s.filter fun i => sign i ≠ 0).card ≤ 2)
    (i : I) (hi : i ∈ s) (hin : sign i ≠ 0) :
    ∃ j ∈ s, j ≠ i ∧ sign j = -sign i ∧
      ∀ k ∈ s, k ≠ i → k ≠ j → sign k = 0 := by
  classical
  have hj : ∃ j ∈ s, j ≠ i ∧ sign j ≠ 0 := by
    by_contra h
    push Not at h
    have hsingle : (∑ k ∈ s, sign k) = sign i := by
      apply Finset.sum_eq_single i
      · intro k hk hki
        exact h k hk hki
      · intro hn
        exact (hn hi).elim
    exact hin (hsingle.symm.trans hsum)
  obtain ⟨j, hj, hji, hjn⟩ := hj
  let S := s.filter fun k => sign k ≠ 0
  have hsub : {i, j} ⊆ S := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hi, hin⟩
    · exact Finset.mem_filter.mpr ⟨hj, hjn⟩
  have heq : S = {i, j} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    simpa only [Finset.card_pair (Ne.symm hji)] using hcard
  have hrestrict : (∑ k ∈ S, sign k) = ∑ k ∈ s, sign k := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hkn
    by_contra hn
    exact hkn (Finset.mem_filter.mpr ⟨hk, hn⟩)
  have hpair : sign i + sign j = 0 := by
    rw [heq, Finset.sum_pair (Ne.symm hji)] at hrestrict
    exact hrestrict.trans hsum
  refine ⟨j, hj, hji, by omega, ?_⟩
  intro k hk hki hkj
  by_contra hn
  have hks : k ∈ S := Finset.mem_filter.mpr ⟨hk, hn⟩
  rw [heq] at hks
  simp only [Finset.mem_insert, Finset.mem_singleton, hki, hkj, or_self] at hks

theorem BalancedIncidenceCycle.moving_pair {L C Q : Type*}
    [Fintype L] [DecidableEq L] [DecidableEq C] [DecidableEq Q]
    {component : L → C} {quartet : L → Q}
    (cycle : BalancedIncidenceCycle component quartet) (i : L) (hi : cycle.sign i ≠ 0) :
    ∃ j : L, quartet j = quartet i ∧ j ≠ i ∧ cycle.sign j = -cycle.sign i ∧
      ∀ k : L, quartet k = quartet i → k ≠ i → k ≠ j → cycle.sign k = 0 := by
  let s := Finset.univ.filter fun k => quartet k = quartet i
  have hc : (s.filter fun k => cycle.sign k ≠ 0).card ≤ 2 := by
    simpa only [s, Finset.filter_filter] using cycle.quartet_support (quartet i)
  obtain ⟨j, hj, hji, hs, hrest⟩ := balanced_two_support_pair s cycle.sign
    (cycle.quartet_balanced (quartet i)) hc i (by simp [s]) hi
  refine ⟨j, (Finset.mem_filter.mp hj).2, hji, hs, ?_⟩
  intro k hk hki hkj
  exact hrest k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩) hki hkj

end Ostmann

end OAI
