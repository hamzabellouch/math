import OAI.Combinatorics.Ramsey.CycleClique.Construction.DistanceLayers
import OAI.Combinatorics.Ramsey.CycleClique.Construction.LayerArithmetic

namespace OAI

/-!
# Parity sums and expansion in the distance layers

The two exact summation identities and the closed neighbourhood inequality
form the counting step of manuscript Proposition `clq:layer-interface`.
-/

namespace CycleClique.Construction
def parityIndices (i : ℕ) : Finset ℕ :=
  (Finset.range (i + 1)).filter (fun j => j % 2 = i % 2)

def alternatingSum (α : ℕ → ℕ) (i : ℕ) : ℕ := ∑ j ∈ parityIndices i, α j

@[simp] theorem alternatingSum_zero (α : ℕ → ℕ) : alternatingSum α 0 = α 0 := by
  simp [alternatingSum, parityIndices, Finset.filter_singleton]

theorem alternatingSum_partition (α : ℕ → ℕ) {i : ℕ} (hi : 1 ≤ i) :
    alternatingSum α i + alternatingSum α (i - 1) = ∑ j ∈ Finset.range (i + 1), α j := by
  have heq : ((Finset.range (i + 1)).filter fun j => ¬ j % 2 = i % 2) =
      parityIndices (i - 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, parityIndices]
    omega
  have h := Finset.sum_filter_add_sum_filter_not
    (Finset.range (i + 1)) (fun j => j % 2 = i % 2) α
  rw [heq] at h
  exact h

theorem alternatingSum_shifted_partition (α : ℕ → ℕ) (hzero : α 0 = 1)
    {i : ℕ} (hi : 1 ≤ i) :
    ∑ j ∈ Finset.range i, α (j + 1) = alternatingSum α i + alternatingSum α (i - 1) - 1 := by
  have h := alternatingSum_partition α hi
  rw [Finset.sum_range_succ', hzero] at h
  omega

theorem alternatingSum_positive (α : ℕ → ℕ) (hzero : 1 ≤ α 0) (hone : 1 ≤ α 1)
    (i : ℕ) : 1 ≤ alternatingSum α i := by
  by_cases heven : i % 2 = 0
  · have hmem : 0 ∈ parityIndices i := by simp [parityIndices, heven]
    have h := Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) hmem
    exact hzero.trans h
  · have hodd : i % 2 = 1 := by omega
    have hipos : 1 ≤ i := by omega
    have hmem : 1 ∈ parityIndices i := by simp [parityIndices, hodd]; omega
    have h := Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) hmem
    exact hone.trans h

theorem indepNum_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.indepNum ≤ Fintype.card V := by
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have := Finset.card_le_univ I
  simpa [hI.card_eq] using this

theorem indepNum_pos_of_nonempty {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : 1 ≤ G.indepNum := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  have hI : G.IsIndepSet (({v} : Finset V) : Set V) := by simp
  simpa using hI.card_le_indepNum

theorem distanceLayer_zero_indepNum {V : Type*} [Fintype V]
    (G : SimpleGraph V) (root : V) :
    (G.induce (distanceLayer G root 0 : Set V)).indepNum = 1 := by
  classical
  rw [distanceLayer_zero]
  let : Nonempty ({root} : Finset V) := ⟨⟨root, by simp⟩⟩
  have hle := indepNum_le_card (G.induce (({root} : Finset V) : Set V))
  have hge := indepNum_pos_of_nonempty (G.induce (({root} : Finset V) : Set V))
  apply Nat.le_antisymm
  · simpa using hle
  · exact hge

theorem distanceLayer_one_nonempty {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) (root : V) :
    (distanceLayer G root 1).Nonempty := by
  classical
  have h := hexpand {root} (by simp) (by simp)
  have hc := closedNeighborhood_singleton_card G root
  have hdegree : 0 < (G.neighborFinset root).card := by
    simp only [Finset.card_singleton, Nat.mul_one, SimpleGraph.ncard_neighborSet,
      ← SimpleGraph.card_neighborFinset_eq_degree] at h hc
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hdegree
  have hadj := (G.mem_neighborFinset root v).mp hv
  exact ⟨v, mem_distanceLayer.mpr ⟨hadj.reachable, SimpleGraph.dist_eq_one_iff_adj.mpr hadj⟩⟩

noncomputable def parityIndependent {V : Type*} [Fintype V]
    (G : SimpleGraph V) (root : V) (i : ℕ) : Finset V := by
  classical
  exact (parityIndices i).biUnion (fun j => independentOn G (distanceLayer G root j))

theorem parityIndependent_independent {V : Type*} [Fintype V]
    (G : SimpleGraph V) (root : V) (i : ℕ) :
    G.IsIndepSet (parityIndependent G root i : Set V) := by
  classical
  intro x hx y hy hxy
  obtain ⟨j, hj, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨l, hl, hy⟩ := Finset.mem_biUnion.mp hy
  by_cases hsame : j = l
  · subst l
    exact independentOn_independent _ _ hx hy hxy
  · apply same_parity_layers_anticomplete hsame
      (((Finset.mem_filter.mp hj).2).trans (Finset.mem_filter.mp hl).2.symm)
    · exact independentOn_subset _ _ hx
    · exact independentOn_subset _ _ hy

theorem parityIndependent_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) (root : V) (i : ℕ) :
    (parityIndependent G root i).card =
      alternatingSum (fun j => (G.induce (distanceLayer G root j : Set V)).indepNum) i := by
  classical
  have hdis : (parityIndices i : Set ℕ).PairwiseDisjoint
      (fun j => independentOn G (distanceLayer G root j)) := by
    intro j _ l _ hjl
    exact (distanceLayers_disjoint G root hjl).mono
      (independentOn_subset _ _) (independentOn_subset _ _)
  simp only [parityIndependent, Finset.card_biUnion hdis, alternatingSum, independentOn_card]

/-- Expansion of the preceding parity union gives the exact first-layer
order inequality used in the density argument. -/
theorem distanceLayer_order_sum {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (root : V) {i : ℕ} (hi : 1 ≤ i) :
    k * alternatingSum (fun j => (G.induce (distanceLayer G root j : Set V)).indepNum) (i - 1) ≤
      ∑ j ∈ Finset.range i, (distanceLayer G root (j + 1)).card := by
  classical
  let α := fun j => (G.induce (distanceLayer G root j : Set V)).indepNum
  have hαzero : α 0 = 1 := distanceLayer_zero_indepNum G root
  have hαone : 1 ≤ α 1 := by
    let : Nonempty (distanceLayer G root 1) :=
      (distanceLayer_one_nonempty hk hexpand root).to_subtype
    exact indepNum_pos_of_nonempty _
  have hpos := alternatingSum_positive α (by omega) hαone (i - 1)
  have hIne : (parityIndependent G root (i - 1)).Nonempty := by
    apply Finset.card_pos.mp
    rw [parityIndependent_card]
    exact hpos
  have hclosed := hexpand _ (parityIndependent_independent G root (i - 1)) hIne
  let U : Finset V := (Finset.range (i + 1)).biUnion (distanceLayer G root)
  have hsub : closedNeighborhood G (parityIndependent G root (i - 1)) ⊆ U := by
    intro y hy
    rcases mem_closedNeighborhood.mp hy with hy | ⟨x, hx, hxy⟩
    · obtain ⟨j, hj, hy⟩ := Finset.mem_biUnion.mp hy
      have hjbound : j < i := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        omega
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by omega), independentOn_subset _ _ hy⟩
    · obtain ⟨j, hj, hx⟩ := Finset.mem_biUnion.mp hx
      have hjbound : j < i := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        omega
      obtain ⟨l, hl, hy⟩ := distanceLayer_neighbor_le (independentOn_subset _ _ hx) hxy
      exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_range.mpr (by omega), hy⟩
  have hdis : ((Finset.range (i + 1)) : Set ℕ).PairwiseDisjoint (distanceLayer G root) := by
    intro j _ l _ hjl
    exact distanceLayers_disjoint G root hjl
  have hU : U.card = ∑ j ∈ Finset.range (i + 1), (distanceLayer G root j).card :=
    Finset.card_biUnion hdis
  have hcard := Finset.card_le_card hsub
  rw [hU, Finset.sum_range_succ', distanceLayer_zero, Finset.card_singleton] at hcard
  rw [parityIndependent_card] at hclosed
  omega

end CycleClique.Construction

end OAI
