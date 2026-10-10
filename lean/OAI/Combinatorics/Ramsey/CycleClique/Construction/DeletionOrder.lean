import OAI.Combinatorics.Ramsey.CycleClique.Construction.ComponentVertices
import OAI.Combinatorics.Ramsey.CycleClique.Construction.EndpointAttachment

namespace OAI

/-! A component of the two-vertex deletion is not a clique and has order at least `2s-2`. -/

namespace CycleClique.Construction
theorem not_clique_of_two_deleted_neighborhoods {V : Type*} [Fintype V]
    {H : SimpleGraph V} {U : Finset V} {y z : V} {s : ℕ}
    (hU : U.Nonempty) (hy : y ∉ U) (hno : H.cliqueNum < s)
    (hdegree : ∀ u ∈ U, s ≤ (H.neighborSet u).ncard)
    (hcover : ∀ u ∈ U, ∀ v, H.Adj u v → v ∈ U ∨ v = y ∨ v = z) :
    ¬ H.IsClique (U : Set V) := by
  classical
  intro hclique
  have hUbound := hclique.card_le_cliqueNum
  have hcover' : ∀ u ∈ U, ∀ v, H.Adj u v → v ∈ (U.erase u) ∪ {y, z} := by
    intro u hu v huv
    rcases hcover u hu v huv with hv | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨huv.ne.symm, hv⟩)
    · simp
    · simp
  have hcard : ∀ u ∈ U, ((U.erase u) ∪ {y, z}).card ≤ U.card + 1 := by
    intro u hu
    have hc := Finset.card_union_le (U.erase u) {y, z}
    have he := Finset.card_erase_add_one hu
    have hp : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨u, hu⟩ := hU
  have hbound := degree_le_of_neighbor_cover (hcover' u hu)
  have hc := hcard u hu
  have hd := hdegree u hu
  have hsize : U.card + 1 = s := by omega
  have hadj : ∀ v ∈ U, H.Adj y v := by
    intro v hv
    apply SimpleGraph.Adj.symm
    apply degree_cover_forces_neighbor (hcover' v hv)
      (show ((U.erase v) ∪ {y, z}).card ≤ (H.neighborSet v).ncard from
        (hcard v hv).trans (hsize.le.trans (hdegree v hv)))
    simp
  have hlarge := clique_extension_size hclique hy hadj
  omega

theorem two_deleted_component_order {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {U : Finset V} {y z : V} {s : ℕ}
    (hnotclique : ¬ H.IsClique (U : Set V))
    (hcover : ∀ u ∈ U, ∀ v, H.Adj u v → v ∈ U ∨ v = y ∨ v = z)
    (hexpand : ∀ a b, a ≠ b → ¬ H.Adj a b →
      2 * s ≤ (closedNeighborhood H {a, b}).card) :
    2 * s - 2 ≤ U.card := by
  classical
  have hex : ∃ a ∈ U, ∃ b ∈ U, a ≠ b ∧ ¬ H.Adj a b := by
    by_contra hn
    apply hnotclique
    intro a ha b hb hab
    by_contra hnab
    exact hn ⟨a, ha, b, hb, hab, hnab⟩
  obtain ⟨a, ha, b, hb, hab, hnot⟩ := hex
  have hsub : closedNeighborhood H {a, b} ⊆ U ∪ {y, z} := by
    intro v hv
    rcases mem_closedNeighborhood.mp hv with hv | ⟨w, hw, hwv⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_union_left _ ha
      · exact Finset.mem_union_left _ hb
    · have hwU : w ∈ U := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact ha
        · exact hb
      rcases hcover w hwU v hwv with hv | rfl | rfl
      · exact Finset.mem_union_left _ hv
      · simp
      · simp
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le U {y, z})
  have hp : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
  have hlow := hexpand a b hab hnot
  omega

end CycleClique.Construction

end OAI
