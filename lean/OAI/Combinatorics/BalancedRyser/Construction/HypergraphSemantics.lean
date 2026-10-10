import OAI.Combinatorics.BalancedRyser.Construction.Hypergraph

namespace OAI

namespace Balanced.PartiteHypergraph
open scoped _root_.Balanced

variable {r n : ℕ}

theorem toHypergraph_edgeSet_eq_image (H : PartiteHypergraph r n) :
    H.toHypergraph.edgeSet =
      (fun e : Fin r → Fin n => (↑(edgeVertices e) : Set (Vertex r n))) ''
        (H.edges : Set (Fin r → Fin n)) := by
  ext E
  simp only [toHypergraph, Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨e, he, hE⟩
    exact ⟨e, he, hE.symm⟩
  · rintro ⟨e, he, hE⟩
    exact ⟨e, he, hE.symm⟩

theorem coe_edgeVertices_injective :
    Function.Injective (fun e : Fin r → Fin n =>
      (↑(edgeVertices e) : Set (Vertex r n))) := by
  intro e f h
  exact edgeVertices_injective (Finset.coe_injective h)

theorem toHypergraph_edgeSet_finite (H : PartiteHypergraph r n) :
    H.toHypergraph.edgeSet.Finite := by
  rw [toHypergraph_edgeSet_eq_image]
  exact H.edges.finite_toSet.image _

theorem toHypergraph_edgeSet_ncard (H : PartiteHypergraph r n) :
    H.toHypergraph.edgeSet.ncard = H.edges.card := by
  rw [toHypergraph_edgeSet_eq_image,
    Set.ncard_image_of_injective _ coe_edgeVertices_injective,
    Set.ncard_coe_finset]

theorem toHypergraph_edge_ncard (H : PartiteHypergraph r n)
    {E : Set (Vertex r n)} (hE : E ∈ H.toHypergraph.edgeSet) : E.ncard = r := by
  obtain ⟨e, _, rfl⟩ := hE
  simp

theorem toHypergraph_edge_inter_part (H : PartiteHypergraph r n)
    {E : Set (Vertex r n)} (hE : E ∈ H.toHypergraph.edgeSet) (i : Fin r) :
    (E ∩ (part (n := n) i : Set (Vertex r n))).ncard = 1 := by
  obtain ⟨e, _, rfl⟩ := hE
  rw [← Finset.coe_inter, Set.ncard_coe_finset, edgeVertices_inter_part]
  simp

theorem toHypergraph_part_ncard (i : Fin r) :
    (part (n := n) i : Set (Vertex r n)).ncard = n := by
  simp

theorem toHypergraph_unique_part (H : PartiteHypergraph r n)
    (v : Vertex r n) :
    v ∈ H.toHypergraph.vertexSet ∧ ∃! i : Fin r, v ∈ part (n := n) i := by
  rcases v with ⟨j, x⟩
  refine ⟨Set.mem_univ _, j, by simp, ?_⟩
  intro i hi
  exact ((mem_part i j x).mp hi).symm

theorem toHypergraph_nonisolated_iff (H : PartiteHypergraph r n) :
    H.Nonisolated ↔ ∀ v ∈ H.toHypergraph.vertexSet,
      ¬ H.toHypergraph.IsIsolated v := by
  classical
  rw [nonisolated_iff_mem_edge]
  constructor
  · intro h v _ hiso
    obtain ⟨e, he, hv⟩ := h v
    exact hiso _ ⟨e, he, rfl⟩ hv
  · intro h v
    by_contra hn
    apply h v (Set.mem_univ _)
    intro E hE hv
    obtain ⟨e, he, rfl⟩ := hE
    exact hn ⟨e, he, hv⟩

theorem toHypergraph_intersecting_iff (H : PartiteHypergraph r n) :
    H.Intersecting ↔ H.toHypergraph.edgeSet.Nonempty ∧
      ∀ E ∈ H.toHypergraph.edgeSet, ∀ F ∈ H.toHypergraph.edgeSet,
        H.toHypergraph.EAdj E F := by
  constructor
  · rintro ⟨hne, h⟩
    obtain ⟨e, he⟩ := hne
    refine ⟨⟨_, e, he, rfl⟩, ?_⟩
    intro E hE F hF
    obtain ⟨e, he, rfl⟩ := hE
    obtain ⟨f, hf, rfl⟩ := hF
    obtain ⟨i, hi⟩ := h e he f hf
    exact ⟨⟨e, he, rfl⟩, ⟨f, hf, rfl⟩, (i, e i), by simp, by simp [hi]⟩
  · rintro ⟨hne, h⟩
    obtain ⟨E, e, he, rfl⟩ := hne
    refine ⟨⟨e, he⟩, ?_⟩
    intro f hf g hg
    obtain ⟨_, _, v, hvf, hvg⟩ := h _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
    exact (edgeVertices_inter_nonempty_iff f g).mp
      ⟨v, Finset.mem_inter.mpr ⟨hvf, hvg⟩⟩

theorem toHypergraph_cover_iff (H : PartiteHypergraph r n)
    (C : Finset (Vertex r n)) :
    H.Covers C ↔ ∀ E ∈ H.toHypergraph.edgeSet,
      ((C : Set (Vertex r n)) ∩ E).Nonempty := by
  rw [covers_iff_inter_nonempty]
  constructor
  · intro h E hE
    obtain ⟨e, he, rfl⟩ := hE
    obtain ⟨v, hv⟩ := h e he
    exact ⟨v, Finset.mem_inter.mp hv⟩
  · intro h e he
    obtain ⟨v, hv⟩ := h _ ⟨e, he, rfl⟩
    exact ⟨v, Finset.mem_inter.mpr hv⟩

theorem toHypergraph_hasCoverNumber_iff (H : PartiteHypergraph r n) (k : ℕ) :
    H.HasCoverNumber k ↔
      (∃ C : Set (Vertex r n),
        (∀ E ∈ H.toHypergraph.edgeSet, (C ∩ E).Nonempty) ∧ C.ncard = k) ∧
      ∀ C : Set (Vertex r n),
        (∀ E ∈ H.toHypergraph.edgeSet, (C ∩ E).Nonempty) → k ≤ C.ncard := by
  classical
  constructor
  · rintro ⟨⟨C, hC, hcard⟩, hmin⟩
    refine ⟨⟨C, (toHypergraph_cover_iff H C).mp hC, by simpa using hcard⟩, ?_⟩
    intro D hD
    have hcover : H.Covers D.toFinite.toFinset := by
      apply (toHypergraph_cover_iff H _).mpr
      simpa using hD
    simpa only [← Set.ncard_eq_toFinset_card] using hmin _ hcover
  · rintro ⟨⟨C, hC, hcard⟩, hmin⟩
    refine ⟨⟨C.toFinite.toFinset, ?_, ?_⟩, ?_⟩
    · apply (toHypergraph_cover_iff H _).mpr
      simpa using hC
    · simpa only [← Set.ncard_eq_toFinset_card] using hcard
    · intro D hD
      simpa using hmin (D : Set (Vertex r n)) ((toHypergraph_cover_iff H D).mp hD)

theorem toHypergraph_matching_card_le_one (H : PartiteHypergraph r n)
    (hH : H.Intersecting) (M : Finset (Set (Vertex r n)))
    (hM : ∀ E ∈ M, E ∈ H.toHypergraph.edgeSet) (hdisj : (M : Set (Set (Vertex r n))).Pairwise Disjoint) :
    M.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro E hE F hF
  by_contra hne
  have hp := (toHypergraph_intersecting_iff H).mp hH
  obtain ⟨_, _, v, hvE, hvF⟩ := hp.2 E (hM E hE) F (hM F hF)
  exact Set.disjoint_left.mp (hdisj hE hF hne) hvE hvF

theorem toHypergraph_exists_matching_card_one (H : PartiteHypergraph r n)
    (hH : H.Intersecting) :
    ∃ M : Finset (Set (Vertex r n)),
      (∀ E ∈ M, E ∈ H.toHypergraph.edgeSet) ∧ (M : Set (Set (Vertex r n))).Pairwise Disjoint ∧ M.card = 1 := by
  classical
  obtain ⟨E, hE⟩ := ((toHypergraph_intersecting_iff H).mp hH).1
  refine ⟨{E}, ?_, ?_, by simp⟩
  · intro F hF
    simpa only [Finset.mem_singleton.mp hF] using hE
  · simp

end Balanced.PartiteHypergraph

namespace Balanced
open scoped _root_.Balanced

theorem balancedCounterexample_set_edge_realization {q : ℕ}
    (h : BalancedCounterexample q) :
    ∃ G : Hypergraph (PartiteHypergraph.Vertex (q + 1) (q + 1)),
      G.vertexSet = Set.univ ∧ G.edgeSet.Finite ∧
      (∀ E ∈ G.edgeSet, E.ncard = q + 1) ∧
      (∀ i : Fin (q + 1),
        (PartiteHypergraph.part (n := q + 1) i : Set
          (PartiteHypergraph.Vertex (q + 1) (q + 1))).ncard = q + 1) ∧
      (∀ v ∈ G.vertexSet, ∃! i : Fin (q + 1),
        v ∈ PartiteHypergraph.part (n := q + 1) i) ∧
      (∀ E ∈ G.edgeSet, ∀ i : Fin (q + 1),
        (E ∩ (PartiteHypergraph.part (n := q + 1) i : Set
          (PartiteHypergraph.Vertex (q + 1) (q + 1)))).ncard = 1) ∧
      (∀ v ∈ G.vertexSet, ¬ G.IsIsolated v) ∧
      (∃ C : Set (PartiteHypergraph.Vertex (q + 1) (q + 1)),
        (∀ E ∈ G.edgeSet, (C ∩ E).Nonempty) ∧ C.ncard = q + 1) ∧
      (∀ C : Set (PartiteHypergraph.Vertex (q + 1) (q + 1)),
        (∀ E ∈ G.edgeSet, (C ∩ E).Nonempty) → q + 1 ≤ C.ncard) ∧
      (∃ M : Finset (Set (PartiteHypergraph.Vertex (q + 1) (q + 1))),
        (∀ E ∈ M, E ∈ G.edgeSet) ∧ (M : Set (Set (PartiteHypergraph.Vertex (q + 1) (q + 1)))).Pairwise Disjoint ∧ M.card = 1) ∧
      (∀ M : Finset (Set (PartiteHypergraph.Vertex (q + 1) (q + 1))),
        (∀ E ∈ M, E ∈ G.edgeSet) → (M : Set (Set (PartiteHypergraph.Vertex (q + 1) (q + 1)))).Pairwise Disjoint → M.card ≤ 1) := by
  obtain ⟨H, hI, hN, hC⟩ := h
  have hcover := (H.toHypergraph_hasCoverNumber_iff (q + 1)).mp hC
  exact ⟨H.toHypergraph, rfl, H.toHypergraph_edgeSet_finite,
    fun _ hE => H.toHypergraph_edge_ncard hE,
    fun i => PartiteHypergraph.toHypergraph_part_ncard i,
    fun v _ => (H.toHypergraph_unique_part v).2,
    fun _ hE i => H.toHypergraph_edge_inter_part hE i,
    H.toHypergraph_nonisolated_iff.mp hN, hcover.1, hcover.2,
    H.toHypergraph_exists_matching_card_one hI,
    fun M hM hd => H.toHypergraph_matching_card_le_one hI M hM hd⟩

end Balanced

end OAI
