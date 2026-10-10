import OAI.Combinatorics.Ramsey.CycleClique.Construction.LayerSums

namespace OAI

/-!
# A dense distance layer

The parity-union expansion and the numerical growth contradiction force
a dense layer among the first `s` layers. The even case is weakly dense;
the odd case is strictly dense, as in Proposition `clq:layer-interface`.
-/

namespace CycleClique.Construction
theorem exists_dense_distance_layer_even {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ} (hs : 1 ≤ s)
    (hInd : IndependenceBound G (2 * s))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      2 * s * I.card + 1 ≤ (closedNeighborhood G I).card) (root : V) :
    ∃ i, 1 ≤ i ∧ i ≤ s ∧ (distanceLayer G root i).Nonempty ∧
      s * (G.induce (distanceLayer G root i : Set V)).indepNum ≤
        (distanceLayer G root i).card := by
  classical
  let α := fun j => (G.induce (distanceLayer G root j : Set V)).indepNum
  let p := alternatingSum α
  have hzero : α 0 = 1 := distanceLayer_zero_indepNum G root
  have hpzero : p 0 = 1 := by simpa [p] using hzero
  have hpbound : p s ≤ 2 * s := by
    simpa [p, α, alternatingSum, parityIndices] using
      parity_layer_independence_bound hInd root s
  have hone := distanceLayer_one_nonempty (by omega : 1 ≤ 2 * s) hexpand root
  by_contra hn
  have hsmall : ∀ j, 1 ≤ j → j ≤ s → (distanceLayer G root j).Nonempty →
      (distanceLayer G root j).card < s * α j := by
    intro j hj hjs hne
    by_contra h
    exact hn ⟨j, hj, hjs, hne, (show s * α j ≤ (distanceLayer G root j).card by omega)⟩
  apply even_layer_growth_contradiction hs p hpzero hpbound
  intro i his
  have hle : ∀ j ∈ Finset.range (i + 1),
      (distanceLayer G root (j + 1)).card ≤ s * α (j + 1) := by
    intro j hj
    by_cases hne : (distanceLayer G root (j + 1)).Nonempty
    · exact (hsmall (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega) hne).le
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  have hsum := Finset.sum_lt_sum hle
    (show ∃ j ∈ Finset.range (i + 1),
      (distanceLayer G root (j + 1)).card < s * α (j + 1) from
      ⟨0, Finset.mem_range.mpr (by omega), by
        simpa using hsmall 1 (by omega) (by omega) hone⟩)
  have hpartition := alternatingSum_shifted_partition α hzero (i := i + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hpartition
  rw [← Finset.mul_sum, hpartition] at hsum
  have hexp := distanceLayer_order_sum (by omega : 1 ≤ 2 * s) hexpand root
    (i := i + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hexp
  exact lt_of_le_of_lt hexp hsum

theorem exists_dense_distance_layer_odd {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ} (hs : 2 ≤ s)
    (hInd : IndependenceBound G (2 * s + 1))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      (2 * s + 1) * I.card + 1 ≤ (closedNeighborhood G I).card) (root : V) :
    ∃ i, 1 ≤ i ∧ i ≤ s ∧ (distanceLayer G root i).Nonempty ∧
      s * (G.induce (distanceLayer G root i : Set V)).indepNum <
        (distanceLayer G root i).card := by
  classical
  let α := fun j => (G.induce (distanceLayer G root j : Set V)).indepNum
  let p := alternatingSum α
  have hzero : α 0 = 1 := distanceLayer_zero_indepNum G root
  have hpzero : p 0 = 1 := by simpa [p] using hzero
  have hpbound : p s ≤ 2 * s + 1 := by
    simpa [p, α, alternatingSum, parityIndices] using
      parity_layer_independence_bound hInd root s
  by_contra hn
  have hsmall : ∀ j, 1 ≤ j → j ≤ s → (distanceLayer G root j).Nonempty →
      (distanceLayer G root j).card ≤ s * α j := by
    intro j hj hjs hne
    by_contra h
    exact hn ⟨j, hj, hjs, hne, (show s * α j < (distanceLayer G root j).card by omega)⟩
  apply odd_layer_growth_contradiction hs p hpzero hpbound
  intro i his
  have hle : ∀ j ∈ Finset.range (i + 1),
      (distanceLayer G root (j + 1)).card ≤ s * α (j + 1) := by
    intro j hj
    by_cases hne : (distanceLayer G root (j + 1)).Nonempty
    · exact hsmall (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega) hne
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  have hsum := Finset.sum_le_sum hle
  have hpartition := alternatingSum_shifted_partition α hzero (i := i + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hpartition
  rw [← Finset.mul_sum, hpartition] at hsum
  have hexp := distanceLayer_order_sum (by omega : 1 ≤ 2 * s + 1) hexpand root
    (i := i + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hexp
  exact hexp.trans hsum

end CycleClique.Construction

end OAI
