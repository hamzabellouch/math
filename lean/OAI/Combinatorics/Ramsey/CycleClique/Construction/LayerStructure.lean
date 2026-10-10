import OAI.Combinatorics.Ramsey.CycleClique.Construction.LayerMinimal
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace OAI

/-!
# Connectivity and nonbipartiteness of a minimum dense subgraph

These are the structural consequences of the minimum-order choice in
manuscript Proposition `clq:layer-interface`.
-/

namespace CycleClique.Construction
/-- Independence numbers add across disjoint anticomplete vertex sets. -/
theorem indepNum_induce_add_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    (A B : Finset V) (hdis : Disjoint A B)
    (hanti : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) :
    (G.induce (A : Set V)).indepNum + (G.induce (B : Set V)).indepNum ≤ G.indepNum := by
  classical
  obtain ⟨I, hI⟩ := (G.induce (A : Set V)).exists_isNIndepSet_indepNum
  obtain ⟨J, hJ⟩ := (G.induce (B : Set V)).exists_isNIndepSet_indepNum
  let I' : Finset V := I.map ⟨Subtype.val, Subtype.val_injective⟩
  let J' : Finset V := J.map ⟨Subtype.val, Subtype.val_injective⟩
  have hIA : I' ⊆ A := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact i.property
  have hJB : J' ⊆ B := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
    exact j.property
  have hI' : G.IsIndepSet (I' : Set V) := by
    intro x hx y hy hxy h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact hI.isIndepSet hi hj (fun h => hxy (congrArg Subtype.val h)) h
  have hJ' : G.IsIndepSet (J' : Set V) := by
    intro x hx y hy hxy h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact hJ.isIndepSet hi hj (fun h => hxy (congrArg Subtype.val h)) h
  have hIJ : G.IsIndepSet ((I' ∪ J' : Finset V) : Set V) := by
    intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · exact hI' hx hy hxy
    · exact hanti x (hIA hx) y (hJB hy)
    · exact fun h => hanti y (hIA hy) x (hJB hx) h.symm
    · exact hJ' hx hy hxy
  have hdis' : Disjoint I' J' := hdis.mono hIA hJB
  have hbound := hIJ.card_le_indepNum
  rw [Finset.card_union_of_disjoint hdis'] at hbound
  simpa [I', J', hI.card_eq, hJ.card_eq] using hbound

private structure DisconnectedPartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  left : Finset V
  right : Finset V
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  cover : left ∪ right = Finset.univ
  disjoint : Disjoint left right
  anticomplete : ∀ x ∈ left, ∀ y ∈ right, ¬ G.Adj x y

private theorem disconnected_partition {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] {G : SimpleGraph V} (hn : ¬ G.Connected) :
    Nonempty (DisconnectedPartition G) := by
  classical
  have hnp : ¬ G.Preconnected := fun h => hn ⟨h⟩
  change ¬ ∀ u v, G.Reachable u v at hnp
  push Not at hnp
  obtain ⟨u, v, huv⟩ := hnp
  let A : Finset V := Finset.univ.filter (G.Reachable u)
  let B : Finset V := Finset.univ.filter (fun x => ¬ G.Reachable u x)
  refine ⟨⟨A, B, ⟨u, by simp [A]⟩, ⟨v, by simp [B, huv]⟩, ?_, ?_, ?_⟩⟩
  · ext x
    simp [A, B]
    exact Classical.em _
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hx).2
  · intro x hx y hy hadj
    exact (Finset.mem_filter.mp hy).2 (((Finset.mem_filter.mp hx).2).trans hadj.reachable)

private theorem DisconnectedPartition.card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (p : DisconnectedPartition G) :
    p.left.card + p.right.card = Fintype.card V := by
  classical
  rw [← Finset.card_union_of_disjoint p.disjoint, p.cover, Finset.card_univ]

/-- A minimum-order induced graph satisfying the even-parameter density
inequality is connected. -/
theorem minimal_dense_connected_even {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {s : ℕ}
    (hdense : s * G.indepNum ≤ Fintype.card V)
    (hminimal : ∀ Y : Finset V, Y.Nonempty → Y.card < Fintype.card V →
      Y.card < s * (G.induce (Y : Set V)).indepNum) : G.Connected := by
  classical
  by_contra hn
  obtain ⟨p⟩ := disconnected_partition hn
  have hsum := p.card
  have hleftPos := Finset.card_pos.mpr p.left_nonempty
  have hrightPos := Finset.card_pos.mpr p.right_nonempty
  have hleft := hminimal p.left p.left_nonempty (by omega)
  have hright := hminimal p.right p.right_nonempty (by omega)
  have hbound := indepNum_induce_add_le p.left p.right p.disjoint p.anticomplete
  have hmul := Nat.mul_le_mul_left s hbound
  rw [Nat.mul_add] at hmul
  omega

/-- A minimum-order induced graph satisfying the odd-parameter strict
density inequality is connected. -/
theorem minimal_dense_connected_odd {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {s : ℕ}
    (hdense : s * G.indepNum < Fintype.card V)
    (hminimal : ∀ Y : Finset V, Y.Nonempty → Y.card < Fintype.card V →
      Y.card ≤ s * (G.induce (Y : Set V)).indepNum) : G.Connected := by
  classical
  by_contra hn
  obtain ⟨p⟩ := disconnected_partition hn
  have hsum := p.card
  have hleftPos := Finset.card_pos.mpr p.left_nonempty
  have hrightPos := Finset.card_pos.mpr p.right_nonempty
  have hleft := hminimal p.left p.left_nonempty (by omega)
  have hright := hminimal p.right p.right_nonempty (by omega)
  have hbound := indepNum_induce_add_le p.left p.right p.disjoint p.anticomplete
  have hmul := Nat.mul_le_mul_left s hbound
  rw [Nat.mul_add] at hmul
  omega

/-- Every bipartite graph has an independent set containing at least
half its vertices. -/
theorem bipartite_order_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hbip : G.IsBipartite) : Fintype.card V ≤ 2 * G.indepNum := by
  classical
  obtain ⟨c⟩ := hbip
  let A : Finset V := Finset.univ.filter (fun v => c v = 0)
  let B : Finset V := Finset.univ.filter (fun v => ¬ c v = 0)
  have hA : G.IsIndepSet (A : Set V) := by
    intro x hx y hy _ hxy
    exact c.valid hxy (((Finset.mem_filter.mp hx).2).trans (Finset.mem_filter.mp hy).2.symm)
  have hB : G.IsIndepSet (B : Set V) := by
    intro x hx y hy _ hxy
    have hx1 := Fin.eq_one_of_ne_zero (c x) (Finset.mem_filter.mp hx).2
    have hy1 := Fin.eq_one_of_ne_zero (c y) (Finset.mem_filter.mp hy).2
    exact c.valid hxy (hx1.trans hy1.symm)
  have hsum : A.card + B.card = Fintype.card V := by
    simpa [A, B] using Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun v => c v = 0)
  have hleft := hA.card_le_indepNum
  have hright := hB.card_le_indepNum
  omega

/-- The dense layer subgraph is nonbipartite. -/
theorem dense_nonbipartite {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {s : ℕ} (hs : 3 ≤ s)
    (hdense : s * G.indepNum ≤ Fintype.card V) : ¬ G.IsBipartite := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  have hsingle : G.IsIndepSet (({v} : Finset V) : Set V) := by simp
  have hpos : 1 ≤ G.indepNum := by simpa using hsingle.card_le_indepNum
  intro hbip
  have := bipartite_order_bound hbip
  nlinarith

/-- Closed singleton neighbourhoods have one more vertex than the degree. -/
theorem closedNeighborhood_singleton_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (closedNeighborhood G {v}).card = (G.neighborSet v).ncard + 1 := by
  classical
  have hclosed : closedNeighborhood G {v} = insert v (G.neighborFinset v) := by
    ext w
    simp [mem_closedNeighborhood]
  have hv : v ∉ G.neighborFinset v := by simp
  rw [hclosed, Finset.card_insert_of_notMem hv]
  simp

/-- The singleton consequence of the dense-minimal expansion bound
gives the minimum degree needed by the coloured-path argument. -/
theorem dense_expansion_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    {s : ℕ} (_hs : 1 ≤ s) (horder : 2 * s ≤ Fintype.card V)
    (hstrict : ∀ v : V, (closedNeighborhood G {v}).card < Fintype.card V →
      s < (closedNeighborhood G {v}).card) :
    ∀ v, s ≤ (G.neighborSet v).ncard := by
  intro v
  have hcard := closedNeighborhood_singleton_card G v
  have hle : (closedNeighborhood G {v}).card ≤ Fintype.card V :=
    Finset.card_le_univ _
  by_cases hfull : (closedNeighborhood G {v}).card = Fintype.card V
  · omega
  · have := hstrict v (by omega)
    omega

end CycleClique.Construction

end OAI
