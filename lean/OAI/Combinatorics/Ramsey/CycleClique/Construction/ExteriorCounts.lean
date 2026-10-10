import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiveCycleGeometry

namespace OAI

/-! Expansion counts after deleting the clique neighbours of an independent set. -/

namespace CycleClique.Construction
theorem exterior_closed_expansion_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q A I B : Finset V} {k : ℕ}
    (hexpand : k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hIA : I ⊆ A) (hAQ : Disjoint A Q)
    (hcover : ∀ i ∈ I, ∀ q ∈ Q, G.Adj i q → q ∈ B) :
    k * I.card + 1 ≤ B.card + (exteriorClosedNeighborhood G Q A).card := by
  classical
  have hsub : closedNeighborhood G I ⊆ B ∪ exteriorClosedNeighborhood G Q A := by
    intro v hv
    by_cases hvQ : v ∈ Q
    · apply Finset.mem_union_left
      rcases mem_closedNeighborhood.mp hv with hvI | ⟨i, hi, hiv⟩
      · exact False.elim (Finset.disjoint_left.mp hAQ (hIA hvI) hvQ)
      · exact hcover i hi v hvQ hiv
    · apply Finset.mem_union_right
      apply mem_exteriorClosedNeighborhood.mpr
      refine ⟨?_, hvQ⟩
      rcases mem_closedNeighborhood.mp hv with hvI | ⟨i, hi, hiv⟩
      · exact Or.inl (hIA hvI)
      · exact Or.inr ⟨i, hIA hi, hiv⟩
  exact hexpand.trans ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))

theorem one_clique_neighbor_expansion {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q A : Finset V} {q : V} {k : ℕ}
    (hA : A.Nonempty) (hAQ : Disjoint A Q)
    (hcover : ∀ a ∈ A, ∀ x ∈ Q, G.Adj a x → x = q)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) :
    k * (G.induce (A : Set V)).indepNum ≤ (exteriorClosedNeighborhood G Q A).card := by
  classical
  let I := independentOn G A
  have hIcard : I.card = (G.induce (A : Set V)).indepNum := independentOn_card G A
  have hpos : 0 < (G.induce (A : Set V)).indepNum := by
    let : Nonempty A := hA.to_subtype
    exact indepNum_pos_of_nonempty _
  have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
  have h := exterior_closed_expansion_bound (B := {q})
    (hexpand I (independentOn_independent G A) hIne) (independentOn_subset G A) hAQ
    (fun i hi x hx hadj => Finset.mem_singleton.mpr
      (hcover i (independentOn_subset G A hi) x hx hadj))
  rw [Finset.card_singleton, hIcard] at h
  omega

theorem exterior_disjoint_sum_bound {V ι : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} (F : Finset ι) (A : ι → Finset V)
    (hdis : (F : Set ι).PairwiseDisjoint (fun i => exteriorClosedNeighborhood G Q (A i))) :
    Q.card + ∑ i ∈ F, (exteriorClosedNeighborhood G Q (A i)).card ≤ Fintype.card V := by
  classical
  let C := F.biUnion (fun i => exteriorClosedNeighborhood G Q (A i))
  have hCcard : C.card = ∑ i ∈ F, (exteriorClosedNeighborhood G Q (A i)).card :=
    Finset.card_biUnion hdis
  have hQC : Disjoint Q C := by
    apply Finset.disjoint_left.mpr
    intro x hx hxC
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hxC
    exact (mem_exteriorClosedNeighborhood.mp hi).2 hx
  have hbound : (Q ∪ C).card ≤ Fintype.card V := by
    simpa only [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ (Q ∪ C))
  rwa [Finset.card_union_of_disjoint hQC, hCcard] at hbound

end CycleClique.Construction

end OAI
