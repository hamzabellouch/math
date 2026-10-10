import OAI.Combinatorics.Ramsey.CycleClique.Construction.DeletedComponent

namespace OAI

/-! Realizing a component of the two-vertex deletion as ambient vertices. -/

namespace CycleClique.Construction
def deletedComponentEmbedding {V : Type*} {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent) : C ↪ V :=
  ⟨fun v => v.val.val, fun _ _ h => Subtype.ext (Subtype.ext h)⟩

noncomputable def componentVertices {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.map (deletedComponentEmbedding C)

@[simp] theorem mem_componentVertices {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z v : V}
    {C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent} :
    v ∈ componentVertices C ↔ ∃ u : C, u.val.val = v := by
  classical
  constructor
  · intro hv
    change v ∈ Finset.univ.map (deletedComponentEmbedding C) at hv
    obtain ⟨u, _, hu⟩ := Finset.mem_map.mp hv
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    change v ∈ Finset.univ.map (deletedComponentEmbedding C)
    exact Finset.mem_map.mpr ⟨u, Finset.mem_univ _, hu⟩

theorem deleted_not_componentVertices {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent) :
    y ∉ componentVertices C ∧ z ∉ componentVertices C := by
  constructor
  · rintro hy
    obtain ⟨u, hu⟩ := mem_componentVertices.mp hy
    exact u.val.property.1 hu
  · rintro hz
    obtain ⟨u, hu⟩ := mem_componentVertices.mp hz
    exact u.val.property.2 hu

theorem componentVertices_neighbor_cover {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent)
    {u v : V} (hu : u ∈ componentVertices C) (h : H.Adj u v) :
    v ∈ componentVertices C ∨ v = y ∨ v = z := by
  obtain ⟨u', rfl⟩ := mem_componentVertices.mp hu
  rcases deleted_component_neighbor_cover C u' h with hy | hz | ⟨w, _, hw⟩
  · exact Or.inr (Or.inl hy)
  · exact Or.inr (Or.inr hz)
  · exact Or.inl (mem_componentVertices.mpr ⟨w, hw⟩)

theorem componentVertices_connected {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent) :
    (H.induce (componentVertices C : Set V)).Connected := by
  classical
  let f : C → (componentVertices C : Set V) := fun u =>
    ⟨u.val.val, mem_componentVertices.mpr ⟨u, rfl⟩⟩
  let φ : C.toSimpleGraph →g H.induce (componentVertices C : Set V) :=
    { toFun := f, map_rel' := fun h => h }
  have hsurj : Function.Surjective φ := by
    intro v
    obtain ⟨u, hu⟩ := mem_componentVertices.mp v.property
    exact ⟨u, Subtype.ext hu⟩
  exact C.connected_toSimpleGraph.map φ hsurj

/-- Restriction to a vertex set closed under all other neighbours loses
at most the two deleted neighbours. -/
theorem induced_degree_loss_pair {V : Type*} [Fintype V]
    {H : SimpleGraph V} {U : Finset V} {y z : V}
    (hcover : ∀ u ∈ U, ∀ v, H.Adj u v → v ∈ U ∨ v = y ∨ v = z)
    (u : (U : Set V)) :
    (H.neighborSet u.val).ncard ≤ ((H.induce (U : Set V)).neighborSet u).ncard + 2 := by
  classical
  let K := H.induce (U : Set V)
  let N : Finset V := (K.neighborFinset u).map ⟨Subtype.val, Subtype.val_injective⟩
  have hsub : H.neighborFinset u.val ⊆ N ∪ {y, z} := by
    intro v hv
    have hadj := (H.mem_neighborFinset u.val v).mp hv
    rcases hcover u.val u.property v hadj with hvU | rfl | rfl
    · let w : (U : Set V) := ⟨v, hvU⟩
      have hw : w ∈ K.neighborFinset u := (K.mem_neighborFinset u w).mpr hadj
      exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨w, hw, rfl⟩)
    · simp
    · simp
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le N {y, z})
  have hpair : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
  have hN : N.card = (K.neighborFinset u).card := Finset.card_map _
  rw [hN] at hcard
  have hdegree : (H.neighborFinset u.val).card ≤ (K.neighborFinset u).card + 2 := by omega
  simpa only [SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.ncard_neighborSet] using hdegree

end CycleClique.Construction

end OAI
