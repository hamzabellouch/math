import OAI.Combinatorics.SharpThreshold.Model

namespace OAI

noncomputable section

namespace Problem313

/-- If a block meets the vertex support in one vertex, precisely that vertex's
incident support edges survive restriction to the block. -/
theorem block_filter_eq_vertex_filter {n : ℕ}
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) (u : Fin n)
    (h : B ∩ S.biUnion (fun e => e.val) = {u}) :
    S.filter (fun e => (e.val ∩ B).Nonempty) =
      S.filter (fun e => u ∈ e.val) := by
  classical
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, v, hv⟩
    have hvB : v ∈ B := (Finset.mem_inter.mp hv).2
    have hvE : v ∈ e.val := (Finset.mem_inter.mp hv).1
    have hvS : v ∈ S.biUnion (fun e => e.val) :=
      Finset.mem_biUnion.mpr ⟨e, he, hvE⟩
    have hvu : v = u := by
      have : v ∈ ({u} : Finset (Fin n)) := h ▸ Finset.mem_inter.mpr ⟨hvB, hvS⟩
      exact Finset.mem_singleton.mp this
    exact ⟨he, hvu ▸ hvE⟩
  · rintro ⟨he, huE⟩
    have hu : u ∈ B ∩ S.biUnion (fun e => e.val) := by rw [h]; simp
    exact ⟨he, u, Finset.mem_inter.mpr ⟨huE, (Finset.mem_inter.mp hu).1⟩⟩

/-- Cardinal version of deterministic capture by a singleton vertex intersection. -/
theorem block_filter_card_eq_vertex_degree {n : ℕ}
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) (u : Fin n)
    (h : B ∩ S.biUnion (fun e => e.val) = {u}) :
    (S.filter (fun e => (e.val ∩ B).Nonempty)).card =
      (S.filter (fun e => u ∈ e.val)).card := by
  rw [block_filter_eq_vertex_filter S B u h]

/-- The singleton-intersection event detects every support with a vertex
of degree between one and the requested cutoff. -/
theorem block_captures_of_singleton_inter {n : ℕ}
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) (u : Fin n) (k : ℝ)
    (h : B ∩ S.biUnion (fun e => e.val) = {u})
    (hpos : 1 ≤ (S.filter (fun e => u ∈ e.val)).card)
    (hdeg : ((S.filter (fun e => u ∈ e.val)).card : ℝ) ≤ k) :
    1 ≤ (S.filter (fun e => (e.val ∩ B).Nonempty)).card ∧
      ((S.filter (fun e => (e.val ∩ B).Nonempty)).card : ℝ) ≤ k := by
  rw [block_filter_card_eq_vertex_degree S B u h]
  exact ⟨hpos, hdeg⟩

/-- The same capture identity with the disjointness predicate used for free edges. -/
theorem block_not_disjoint_filter_eq_vertex_filter {n : ℕ}
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) (u : Fin n)
    (h : B ∩ S.biUnion (fun e => e.val) = {u}) :
    S.filter (fun e => ¬Disjoint e.val B) =
      S.filter (fun e => u ∈ e.val) := by
  classical
  simpa only [Finset.not_disjoint_iff, Finset.Nonempty, Finset.mem_inter] using
    block_filter_eq_vertex_filter S B u h

/-- The free-edge intersection formulation of deterministic block capture. -/
theorem block_inter_free_edges_eq_vertex_filter {n : ℕ}
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) (u : Fin n)
    (h : B ∩ S.biUnion (fun e => e.val) = {u}) :
    S ∩ Finset.univ.filter (fun e : GraphEdge n => ¬Disjoint e.val B) =
      S.filter (fun e => u ∈ e.val) := by
  classical
  rw [← block_not_disjoint_filter_eq_vertex_filter S B u h]
  ext e
  simp

/-- Counting singleton-intersection blocks gives a lower bound for counting
blocks that capture the support in the desired degree range. -/
theorem count_capturing_blocks_ge_singleton_inter {n : ℕ}
    (S : Finset (GraphEdge n)) (blocks : Finset (Finset (Fin n)))
    (u : Fin n) (k : ℝ)
    (hpos : 1 ≤ (S.filter (fun e => u ∈ e.val)).card)
    (hdeg : ((S.filter (fun e => u ∈ e.val)).card : ℝ) ≤ k) :
    (blocks.filter (fun B => B ∩ S.biUnion (fun e => e.val) = {u})).card ≤
      (blocks.filter (fun B =>
        1 ≤ (S.filter (fun e => (e.val ∩ B).Nonempty)).card ∧
        ((S.filter (fun e => (e.val ∩ B).Nonempty)).card : ℝ) ≤ k)).card := by
  classical
  apply Finset.card_le_card
  intro B hB
  obtain ⟨hmem, hsingle⟩ := Finset.mem_filter.mp hB
  exact Finset.mem_filter.mpr
    ⟨hmem, block_captures_of_singleton_inter S B u k hsingle hpos hdeg⟩

end Problem313

end

end OAI
