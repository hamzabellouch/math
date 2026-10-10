import OAI.Combinatorics.Ramsey.CycleClique.Construction.SmallCycleGeometry

namespace OAI

/-! Exterior edges and two-edge paths which close to an exact five-cycle. -/

namespace CycleClique.Construction
private theorem clique_third_vertex {V : Type*} [DecidableEq V] {Q : Finset V}
    (hQcard : 3 ≤ Q.card) {x y : V} (hxy : x ≠ y) :
    ∃ z ∈ Q, z ≠ x ∧ z ≠ y := by
  obtain ⟨z, hz, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({x, y} : Finset V).card < Q.card by rw [Finset.card_pair hxy]; omega)
  exact ⟨z, hz, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hnot⟩

theorem fiveCycle_triangle_exterior_no_edge {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} (hQ : G.IsClique (Q : Set V)) (hQcard : 3 ≤ Q.card)
    (hcycle : ¬ HasCycle G 5) {x y u v : V} (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y)
    (hu : u ∈ exteriorNeighbors G Q x) (hv : v ∈ exteriorNeighbors G Q y) : ¬ G.Adj u v := by
  classical
  obtain ⟨z, hzQ, hzx, hzy⟩ := clique_third_vertex hQcard hxy
  obtain ⟨hxu, huQ⟩ := mem_exteriorNeighbors.mp hu
  obtain ⟨hyv, hvQ⟩ := mem_exteriorNeighbors.mp hv
  intro huv
  have hnd : ([x, u, v, y, z] : List V).Nodup := by
    simp [hxu.ne, ne_of_mem_of_not_mem hx hvQ, hxy, hzx.symm, huv.ne,
      ne_of_mem_of_not_mem hy huQ |>.symm, ne_of_mem_of_not_mem hzQ huQ |>.symm,
      hyv.ne.symm, ne_of_mem_of_not_mem hzQ hvQ |>.symm, hzy.symm]
  exact hcycle (hasCycle_five_of_edges hnd hxu huv hyv.symm (hQ hy hzQ hzy.symm) (hQ hzQ hx hzx))

theorem fiveCycle_triangle_exterior_no_common {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G 5) {x y u v z : V} (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y)
    (hu : u ∈ exteriorNeighbors G Q x) (hv : v ∈ exteriorNeighbors G Q y)
    (huv : u ≠ v) (hzQ : z ∉ Q) : ¬ (G.Adj u z ∧ G.Adj v z) := by
  classical
  obtain ⟨hxu, huQ⟩ := mem_exteriorNeighbors.mp hu
  obtain ⟨hyv, hvQ⟩ := mem_exteriorNeighbors.mp hv
  rintro ⟨huz, hvz⟩
  have hnd : ([x, u, z, v, y] : List V).Nodup := by
    simp [hxu.ne, ne_of_mem_of_not_mem hx hzQ, ne_of_mem_of_not_mem hx hvQ, hxy,
      huz.ne, huv, ne_of_mem_of_not_mem hy huQ |>.symm, hvz.ne.symm,
      ne_of_mem_of_not_mem hy hzQ |>.symm, hyv.ne.symm]
  exact hcycle (hasCycle_five_of_edges hnd hxu huz hvz.symm hyv.symm (hQ hy hx hxy.symm))

theorem fiveCycle_fourClique_exterior_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} (hQ : G.IsClique (Q : Set V)) (hQcard : Q.card = 4)
    (hcycle : ¬ HasCycle G 5) {x y : V} (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y) :
    Disjoint (exteriorNeighbors G Q x) (exteriorNeighbors G Q y) := by
  classical
  let R := Q \ {x, y}
  have hsub : ({x, y} : Finset V) ⊆ Q := by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hx, hy⟩
  have hRcard : R.card = 2 := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    rw [Finset.card_pair hxy, hQcard] at h
    change R.card + 2 = 4 at h
    omega
  obtain ⟨z, hz, w, hw, hzw⟩ := Finset.one_lt_card.mp (by omega : 1 < R.card)
  have hzQ := (Finset.mem_sdiff.mp hz).1
  have hwQ := (Finset.mem_sdiff.mp hw).1
  have hznot : z ≠ x ∧ z ≠ y := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using (Finset.mem_sdiff.mp hz).2
  have hwnot : w ≠ x ∧ w ≠ y := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using (Finset.mem_sdiff.mp hw).2
  apply Finset.disjoint_left.mpr
  intro u hu hv
  obtain ⟨hxu, huQ⟩ := mem_exteriorNeighbors.mp hu
  obtain ⟨hyu, _⟩ := mem_exteriorNeighbors.mp hv
  have hnd : ([x, u, y, z, w] : List V).Nodup := by
    simp [hxu.ne, hxy, hznot.1.symm, hwnot.1.symm, hyu.ne.symm,
      ne_of_mem_of_not_mem hzQ huQ |>.symm, ne_of_mem_of_not_mem hwQ huQ |>.symm,
      hznot.2.symm, hwnot.2.symm, hzw]
  exact hcycle (hasCycle_five_of_edges hnd hxu hyu.symm (hQ hy hzQ hznot.2.symm)
    (hQ hzQ hwQ hzw) (hQ hwQ hx hwnot.1))

noncomputable def exteriorClosedNeighborhood {V : Type*} [Fintype V]
    (G : SimpleGraph V) (Q A : Finset V) : Finset V := by
  classical
  exact closedNeighborhood G A \ Q

@[simp] theorem mem_exteriorClosedNeighborhood {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q A : Finset V} {v : V} :
    v ∈ exteriorClosedNeighborhood G Q A ↔
      (v ∈ A ∨ ∃ a ∈ A, G.Adj a v) ∧ v ∉ Q := by
  classical
  simp only [exteriorClosedNeighborhood, Finset.mem_sdiff, mem_closedNeighborhood]

theorem exteriorClosedNeighborhood_disjoint {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q A B : Finset V} (hdis : Disjoint A B)
    (hanti : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hcommon : ∀ a ∈ A, ∀ b ∈ B, ∀ z, z ∉ Q → ¬ (G.Adj a z ∧ G.Adj b z)) :
    Disjoint (exteriorClosedNeighborhood G Q A) (exteriorClosedNeighborhood G Q B) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hzA hzB
  obtain ⟨hza, hzQ⟩ := mem_exteriorClosedNeighborhood.mp hzA
  obtain ⟨hzb, _⟩ := mem_exteriorClosedNeighborhood.mp hzB
  rcases hza with hza | ⟨a, ha, haz⟩ <;> rcases hzb with hzb | ⟨b, hb, hbz⟩
  · exact Finset.disjoint_left.mp hdis hza hzb
  · exact hanti z hza b hb hbz.symm
  · exact hanti a ha z hzb haz
  · exact hcommon a ha b hb z hzQ ⟨haz, hbz⟩

theorem fiveCycle_exterior_closed_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} (hQ : G.IsClique (Q : Set V)) (hQcard : 3 ≤ Q.card)
    (hcycle : ¬ HasCycle G 5) {x y : V} (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y)
    {A B : Finset V} (hA : A ⊆ exteriorNeighbors G Q x) (hB : B ⊆ exteriorNeighbors G Q y)
    (hdis : Disjoint A B) :
    Disjoint (exteriorClosedNeighborhood G Q A) (exteriorClosedNeighborhood G Q B) := by
  apply exteriorClosedNeighborhood_disjoint hdis
  · intro a ha b hb
    exact fiveCycle_triangle_exterior_no_edge hQ hQcard hcycle hx hy hxy (hA ha) (hB hb)
  · intro a ha b hb z hzQ
    have hab : a ≠ b := fun he => Finset.disjoint_left.mp hdis ha (he ▸ hb)
    exact fiveCycle_triangle_exterior_no_common hQ hcycle hx hy hxy (hA ha) (hB hb) hab hzQ

end CycleClique.Construction

end OAI
