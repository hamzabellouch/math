import OAI.Combinatorics.Ramsey.CycleClique.Construction.EndpointTail

namespace OAI

/-! The degree calculations forcing a second attachment and a common neighbour. -/

namespace CycleClique.Construction
theorem degree_le_of_neighbor_cover {V : Type*} [Fintype V]
    {H : SimpleGraph V} {v : V} {S : Finset V}
    (hcover : ∀ w, H.Adj v w → w ∈ S) : (H.neighborSet v).ncard ≤ S.card := by
  classical
  have hsub : H.neighborFinset v ⊆ S := fun w hw =>
    hcover w ((H.mem_neighborFinset v w).mp hw)
  simpa only [SimpleGraph.ncard_neighborSet,
    SimpleGraph.card_neighborFinset_eq_degree] using Finset.card_le_card hsub

theorem degree_cover_forces_neighbor {V : Type*} [Fintype V]
    {H : SimpleGraph V} {v w : V} {S : Finset V}
    (hcover : ∀ a, H.Adj v a → a ∈ S)
    (hdegree : S.card ≤ (H.neighborSet v).ncard) (hw : w ∈ S) : H.Adj v w := by
  classical
  have hsub : H.neighborFinset v ⊆ S := fun a ha =>
    hcover a ((H.mem_neighborFinset v a).mp ha)
  have hcard : S.card ≤ (H.neighborFinset v).card := by
    simpa only [SimpleGraph.ncard_neighborSet,
      SimpleGraph.card_neighborFinset_eq_degree] using hdegree
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  exact (H.mem_neighborFinset v w).mp (heq.symm ▸ hw)

theorem clique_extension_size {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {E : Finset V} {u : V}
    (hclique : H.IsClique (E : Set V)) (hu : u ∉ E)
    (hadj : ∀ w ∈ E, H.Adj u w) : E.card + 1 ≤ H.cliqueNum := by
  have hQ : H.IsClique ((insert u E : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    exact hclique.insert (fun w hw _ => hadj w hw)
  have h := hQ.card_le_cliqueNum
  simpa only [Finset.card_insert_of_notMem hu] using h

private theorem erased_pair_cover_card {V : Type*} [DecidableEq V]
    {E : Finset V} {w y z : V} (hw : w ∈ E) :
    ((E.erase w) ∪ {y, z}).card ≤ E.card + 1 := by
  have h := Finset.card_union_le (E.erase w) {y, z}
  have he := Finset.card_erase_add_one hw
  have hp : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
  omega

/-- The attachment vertex has a second neighbour in the endpoint
clique; this is the two-case degree calculation in the manuscript. -/
theorem endpoint_second_attachment {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {E : Finset V} {u w₀ y z : V} {s : ℕ}
    (hs : 4 ≤ s) (hsize : s - 2 ≤ E.card ∧ E.card ≤ s - 1)
    (hclique : H.IsClique (E : Set V)) (hno : H.cliqueNum < s)
    (hy : y ∉ E) (hz : z ∉ E) (hw₀ : w₀ ∈ E)
    (hdegree : ∀ w ∈ E, s ≤ (H.neighborSet w).ncard)
    (hpartial : ∀ w ∈ E, w ≠ w₀ → ∀ v, H.Adj w v →
      v ∈ (E.erase w) ∪ {u, y, z})
    (hzero : ¬ H.Adj w₀ y → ¬ H.Adj w₀ z → (H.neighborSet w₀).ncard ≤ E.card) :
    ∃ w ∈ E, w ≠ w₀ ∧ H.Adj u w := by
  classical
  by_contra hn
  have hnotu : ∀ w ∈ E, w ≠ w₀ → ¬ H.Adj w u := by
    intro w hw hne hwu
    exact hn ⟨w, hw, hne, hwu.symm⟩
  have hcover : ∀ w ∈ E, w ≠ w₀ → ∀ v, H.Adj w v →
      v ∈ (E.erase w) ∪ {y, z} := by
    intro w hw hne v hwv
    rcases Finset.mem_union.mp (hpartial w hw hne v hwv) with hv | hv
    · exact Finset.mem_union_left _ hv
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact False.elim (hnotu w hw hne hwv)
      · simp
      · simp
  by_cases hsmall : E.card = s - 2
  · obtain ⟨w, hw, hne⟩ := Finset.exists_mem_ne (by omega : 1 < E.card) w₀
    have hbound := degree_le_of_neighbor_cover (hcover w hw hne)
    have hcard := erased_pair_cover_card (y := y) (z := z) hw
    have hlow := hdegree w hw
    omega
  · have hlarge : E.card = s - 1 := by omega
    have hboth : ∀ w ∈ E, w ≠ w₀ → H.Adj w y ∧ H.Adj w z := by
      intro w hw hne
      have hc := erased_pair_cover_card (y := y) (z := z) hw
      have hd := hdegree w hw
      have hforce : ∀ a ∈ (E.erase w) ∪ {y, z}, H.Adj w a := fun a ha =>
        degree_cover_forces_neighbor (hcover w hw hne)
          (show ((E.erase w) ∪ {y, z}).card ≤ (H.neighborSet w).ncard by omega) ha
      exact ⟨hforce y (by simp), hforce z (by simp)⟩
    have hsome : H.Adj w₀ y ∨ H.Adj w₀ z := by
      by_contra hn
      have hny : ¬ H.Adj w₀ y := fun h => hn (Or.inl h)
      have hnz : ¬ H.Adj w₀ z := fun h => hn (Or.inr h)
      have h := hzero hny hnz
      have h' := hdegree w₀ hw₀
      omega
    rcases hsome with hwy | hwz
    · have hadj : ∀ w ∈ E, H.Adj y w := by
        intro w hw
        by_cases heq : w = w₀
        · subst w; exact hwy.symm
        · exact (hboth w hw heq).1.symm
      have h := clique_extension_size hclique hy hadj
      omega
    · have hadj : ∀ w ∈ E, H.Adj z w := by
        intro w hw
        by_cases heq : w = w₀
        · subst w; exact hwz.symm
        · exact (hboth w hw heq).2.symm
      have h := clique_extension_size hclique hz hadj
      omega

/-- Once all endpoints attach only through `u`, one endpoint sees both
deleted vertices. -/
theorem endpoint_common_deleted_neighbor {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {E : Finset V} {u y z : V} {s : ℕ}
    (hs : 4 ≤ s) (hsize : s - 2 ≤ E.card ∧ E.card ≤ s - 1)
    (hclique : H.IsClique (E : Set V)) (hno : H.cliqueNum < s) (hu : u ∉ E)
    (hdegree : ∀ w ∈ E, s ≤ (H.neighborSet w).ncard)
    (hcover : ∀ w ∈ E, ∀ v, H.Adj w v → v ∈ (E.erase w) ∪ {u, y, z}) :
    ∃ w ∈ E, H.Adj w y ∧ H.Adj w z := by
  classical
  by_cases hsmall : E.card = s - 2
  · obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
    have hc := Finset.card_union_le (E.erase w) {u, y, z}
    have he := Finset.card_erase_add_one hw
    have ht : ({u, y, z} : Finset V).card ≤ 3 := Finset.card_le_three
    have hd := hdegree w hw
    have hforce : ∀ a ∈ (E.erase w) ∪ {u, y, z}, H.Adj w a := fun a ha =>
      degree_cover_forces_neighbor (hcover w hw)
        (show ((E.erase w) ∪ {u, y, z}).card ≤ (H.neighborSet w).ncard by omega) ha
    exact ⟨w, hw, hforce y (by simp), hforce z (by simp)⟩
  · have hlarge : E.card = s - 1 := by omega
    by_contra hn
    have hadju : ∀ w ∈ E, H.Adj u w := by
      intro w hw
      by_contra hnu
      have hnotu : ¬ H.Adj w u := fun h => hnu h.symm
      have hpair : ¬ H.Adj w y ∨ ¬ H.Adj w z := by
        by_cases hwy : H.Adj w y
        · exact Or.inr (fun hwz => hn ⟨w, hw, hwy, hwz⟩)
        · exact Or.inl hwy
      have hbound : (H.neighborSet w).ncard ≤ E.card := by
        rcases hpair with hny | hnz
        · have hsub : ∀ v, H.Adj w v → v ∈ insert z (E.erase w) := by
            intro v hwv
            rcases Finset.mem_union.mp (hcover w hw v hwv) with hv | hv
            · exact Finset.mem_insert_of_mem hv
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
              rcases hv with rfl | rfl | rfl
              · exact False.elim (hnotu hwv)
              · exact False.elim (hny hwv)
              · simp
          have h := degree_le_of_neighbor_cover hsub
          have hc := Finset.card_insert_le z (E.erase w)
          have he := Finset.card_erase_add_one hw
          omega
        · have hsub : ∀ v, H.Adj w v → v ∈ insert y (E.erase w) := by
            intro v hwv
            rcases Finset.mem_union.mp (hcover w hw v hwv) with hv | hv
            · exact Finset.mem_insert_of_mem hv
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
              rcases hv with rfl | rfl | rfl
              · exact False.elim (hnotu hwv)
              · simp
              · exact False.elim (hnz hwv)
          have h := degree_le_of_neighbor_cover hsub
          have hc := Finset.card_insert_le y (E.erase w)
          have he := Finset.card_erase_add_one hw
          omega
      have hlow := hdegree w hw
      omega
    have h := clique_extension_size hclique hu hadju
    omega

end CycleClique.Construction

end OAI
