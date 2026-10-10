import OAI.Combinatorics.Ramsey.CycleClique.Construction.FullLargeClique
import OAI.Combinatorics.Ramsey.CycleClique.Construction.WalkCycle

namespace OAI

/-! Exact short-cycle constructions and exterior-neighbour counts for Section 4. -/

namespace CycleClique.Construction
theorem hasCycle_of_closed_list {V : Type*} {G : SimpleGraph V} (L : List V)
    (hnd : L.Nodup) (hchain : L.IsChain G.Adj) (hlen : 3 ≤ L.length)
    (hclose : ∀ a ∈ L.head?, ∀ b ∈ L.getLast?, G.Adj b a) : HasCycle G L.length := by
  have hne : L ≠ [] := by intro h; simp [h] at hlen
  let p := SimpleGraph.Walk.ofSupport L hne hchain
  have hp : p.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simpa only [p, SimpleGraph.Walk.support_ofSupport] using hnd
  have hplength : p.length = L.length - 1 := SimpleGraph.Walk.length_ofSupport hne hchain
  have hedge : G.Adj (L.getLast hne) (L.head hne) :=
    hclose _ (List.head?_eq_some_head hne) _ (List.getLast?_eq_some_getLast hne)
  have hcycle := hasCycle_of_path_close hp (by omega) hedge
  have hlen' : p.length + 1 = L.length := by omega
  simpa only [hlen'] using hcycle

theorem hasCycle_four_of_edges {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : HasCycle G 4 := by
  have hab' := hab.ne
  have hbc' := hbc.ne
  have hcd' := hcd.ne
  have hda' := hda.ne
  have hnd : ([a, b, c, d] : List V).Nodup := by simp [hab', hbc', hcd', hda'.symm, hac, hbd]
  have h := hasCycle_of_closed_list (G := G) [a, b, c, d] hnd
    (by simp [List.isChain_cons_cons, hab, hbc, hcd]) (by simp) (by simpa using hda)
  exact h

theorem hasCycle_five_of_edges {V : Type*} {G : SimpleGraph V} {a b c d e : V}
    (hnd : ([a, b, c, d, e] : List V).Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hea : G.Adj e a) : HasCycle G 5 := by
  exact hasCycle_of_closed_list [a, b, c, d, e] hnd
    (by simp [List.isChain_cons_cons, hab, hbc, hcd, hde]) (by simp) (by simpa using hea)

noncomputable def exteriorNeighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) (Q : Finset V) (q : V) : Finset V := by
  classical
  exact G.neighborFinset q \ Q

@[simp] theorem mem_exteriorNeighbors {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Finset V} {q v : V} :
    v ∈ exteriorNeighbors G Q q ↔ G.Adj q v ∧ v ∉ Q := by
  classical
  simp only [exteriorNeighbors, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]

theorem exteriorNeighbors_card_lower {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} {q : V} {k : ℕ} (hq : q ∈ Q)
    (hexpand : k + 1 ≤ (closedNeighborhood G {q}).card) :
    k + 1 ≤ Q.card + (exteriorNeighbors G Q q).card := by
  classical
  have hsub : closedNeighborhood G {q} ⊆ Q ∪ exteriorNeighbors G Q q := by
    intro v hv
    by_cases hvQ : v ∈ Q
    · exact Finset.mem_union_left _ hvQ
    · apply Finset.mem_union_right
      apply mem_exteriorNeighbors.mpr
      refine ⟨?_, hvQ⟩
      rcases mem_closedNeighborhood.mp hv with hv | ⟨u, hu, huv⟩
      · have heq : v = q := Finset.mem_singleton.mp hv
        exact False.elim (hvQ (heq ▸ hq))
      · have heq : u = q := Finset.mem_singleton.mp hu
        simpa only [heq] using huv
  exact hexpand.trans ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))

/-- Outside a triangle, a common neighbour of two triangle vertices creates a four-cycle. -/
theorem fourCycle_triangle_exterior_disjoint {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Finset V} (hQ : G.IsClique (Q : Set V)) (hQcard : Q.card = 3)
    (hcycle : ¬ HasCycle G 4) {x y : V} (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y) :
    Disjoint (exteriorNeighbors G Q x) (exteriorNeighbors G Q y) := by
  classical
  have hsmall : ({x, y} : Finset V).card < Q.card := by simp only [Finset.card_pair hxy, hQcard]; omega
  obtain ⟨z, hzQ, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hnot : z ≠ x ∧ z ≠ y := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hz
  have hzx : z ≠ x := hnot.1
  have hzy : z ≠ y := hnot.2
  apply Finset.disjoint_left.mpr
  intro u hu hv
  obtain ⟨hxu, huQ⟩ := mem_exteriorNeighbors.mp hu
  obtain ⟨hyu, _⟩ := mem_exteriorNeighbors.mp hv
  exact hcycle (hasCycle_four_of_edges hxu hyu.symm (hQ hy hzQ hzy.symm)
    (hQ hzQ hx hzx) hxy (ne_of_mem_of_not_mem hzQ huQ).symm)

/-- Edges between two triangle exterior classes create a four-cycle. -/
theorem fourCycle_triangle_exterior_anticomplete {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Finset V} (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G 4) {x y u v : V}
    (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y)
    (hu : u ∈ exteriorNeighbors G Q x) (hv : v ∈ exteriorNeighbors G Q y) :
    ¬ G.Adj u v := by
  obtain ⟨hxu, huQ⟩ := mem_exteriorNeighbors.mp hu
  obtain ⟨hyv, hvQ⟩ := mem_exteriorNeighbors.mp hv
  intro huv
  exact hcycle (hasCycle_four_of_edges hxu huv hyv.symm (hQ hy hx hxy.symm)
    (ne_of_mem_of_not_mem hx hvQ) (ne_of_mem_of_not_mem hy huQ).symm)

end CycleClique.Construction

end OAI
