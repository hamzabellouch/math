import OAI.Combinatorics.Ramsey.CycleClique.Construction.LongestPaths

namespace OAI

/-! Components after deleting the two common neighbours' endpoints. -/

namespace CycleClique.Construction
/-- A neighbour of a vertex in a component after deleting `y,z` is
either one of these two vertices or a neighbour in that component. -/
theorem deleted_component_neighbor_cover {V : Type*} {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent)
    (u : C) {v : V} (h : H.Adj u.val.val v) :
    v = y ∨ v = z ∨ ∃ w : C, C.toSimpleGraph.Adj u w ∧ w.val.val = v := by
  by_cases hy : v = y
  · exact Or.inl hy
  by_cases hz : v = z
  · exact Or.inr (Or.inl hz)
  let w : {v : V | v ≠ y ∧ v ≠ z} := ⟨v, hy, hz⟩
  have hadj : (H.induce {v | v ≠ y ∧ v ≠ z}).Adj u.val w := h
  have hw := C.mem_supp_of_adj_mem_supp u.property hadj
  exact Or.inr (Or.inr ⟨⟨w, hw⟩, hadj, rfl⟩)

theorem deleted_component_degree_loss {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent) (u : C) :
    (H.neighborSet u.val.val).ncard ≤ (C.toSimpleGraph.neighborSet u).ncard + 2 := by
  classical
  let f : C → V := fun v => v.val.val
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact Subtype.ext h
  let N : Finset V := (C.toSimpleGraph.neighborFinset u).map ⟨f, hf⟩
  have hsub : H.neighborFinset u.val.val ⊆ N ∪ {y, z} := by
    intro v hv
    have hadj := (H.mem_neighborFinset u.val.val v).mp hv
    rcases deleted_component_neighbor_cover C u hadj with rfl | rfl | ⟨w, hw, rfl⟩
    · simp
    · simp
    · exact Finset.mem_union_left _ (Finset.mem_map.mpr
        ⟨w, (C.toSimpleGraph.mem_neighborFinset u w).mpr hw, rfl⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le N {y, z})
  have hpair : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
  have hN : N.card = (C.toSimpleGraph.neighborFinset u).card := Finset.card_map _
  rw [hN] at hcard
  have hdegree : (H.neighborFinset u.val.val).card ≤
      (C.toSimpleGraph.neighborFinset u).card + 2 := by omega
  simpa only [SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.ncard_neighborSet] using hdegree

theorem deleted_component_min_degree {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z : V} {s : ℕ}
    (hdegree : ∀ v, s ≤ (H.neighborSet v).ncard)
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent) :
    ∀ u : C, s - 2 ≤ (C.toSimpleGraph.neighborSet u).ncard := by
  intro u
  have h := deleted_component_degree_loss C u
  have h' := hdegree u.val.val
  omega

theorem deleted_component_cliqueNum_le {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent) :
    C.toSimpleGraph.cliqueNum ≤ H.cliqueNum := by
  exact ((H.induce {v | v ≠ y ∧ v ≠ z}).cliqueNum_induce_le C.supp).trans
    (H.cliqueNum_induce_le _)

end CycleClique.Construction

end OAI
