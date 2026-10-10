import OAI.Combinatorics.GraphThreshold.GraphContainment

namespace OAI

noncomputable section

open scoped Pointwise

namespace LeanBlast.SecondKahnKalai

variable {n : ℕ}

/-- The subgraph containing exactly the given edges and their incident vertices.
For the empty edge set this has no vertices, as required for internal copies. -/
def edgeSubgraph (S : Finset (Edge n)) : (⊤ : SimpleGraph (Fin n)).Subgraph where
  verts := (graphOfEdges S).support
  Adj := (graphOfEdges S).Adj
  adj_sub h := h.ne
  edge_vert h := ⟨_, h⟩
  symm := (graphOfEdges S).symm

def edgeSupportGraph (S : Finset (Edge n)) :
    SimpleGraph (graphOfEdges S).support := (edgeSubgraph S).coe

@[simp]
theorem edgeSubgraph_spanningCoe (S : Finset (Edge n)) :
    (edgeSubgraph S).spanningCoe = graphOfEdges S := rfl

@[simp]
theorem edgeSupportGraph_map (S : Finset (Edge n)) :
    (edgeSupportGraph S).map (Function.Embedding.subtype
      (fun v => v ∈ (graphOfEdges S).support)) = graphOfEdges S := by
  exact SimpleGraph.Subgraph.spanningCoe_coe (edgeSubgraph S)

theorem edgeSupportGraph_noIsolates (S : Finset (Edge n))
    (v : (graphOfEdges S).support) :
    ∃ w, (edgeSupportGraph S).Adj v w := by
  obtain ⟨w, hw⟩ := v.property
  have hvw : (graphOfEdges S).Adj v w := hw
  exact ⟨⟨w, ⟨v, hvw.symm⟩⟩, hvw⟩

/-- Restriction of a graph isomorphism to its incident vertices. -/
def supportIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : G.induce G.support ≃g H.induce H.support where
  toFun v := ⟨e v, by
    obtain ⟨w, hw⟩ := v.property
    exact ⟨e w, e.toHom.map_adj hw⟩⟩
  invFun v := ⟨e.symm v, by
    obtain ⟨w, hw⟩ := v.property
    exact ⟨e.symm w, e.symm.toHom.map_adj hw⟩⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v)
  right_inv v := Subtype.ext (e.apply_symm_apply v)
  map_rel_iff' := e.map_rel_iff

def edgeSupportGraph_smulIso (σ : Equiv.Perm (Fin n)) (S : Finset (Edge n)) :
    edgeSupportGraph S ≃g edgeSupportGraph (σ • S) := by
  have e : graphOfEdges S ≃g graphOfEdges (σ • S) := by
    rw [graphOfEdges_smul]
    exact SimpleGraph.Iso.map σ _
  exact supportIso e

theorem map_eq_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : G.map e.toEquiv.toEmbedding = H := by
  ext a b
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨v, w, hvw, rfl, rfl⟩
    exact e.toHom.map_adj hvw
  · intro hab
    exact ⟨e.symm a, e.symm b, e.symm.toHom.map_adj hab,
      e.apply_symm_apply a, e.apply_symm_apply b⟩

/-- An isomorphism of incident-vertex graphs extends to a permutation of the
full ambient vertex set, hence to equality of the corresponding edge copies. -/
theorem exists_smul_eq_of_edgeSupportGraph_iso {S T : Finset (Edge n)}
    (e : edgeSupportGraph S ≃g edgeSupportGraph T) :
    ∃ σ : Equiv.Perm (Fin n), σ • S = T := by
  let f : (graphOfEdges S).support ↪ Fin n := Function.Embedding.subtype _
  let j : (graphOfEdges T).support ↪ Fin n := Function.Embedding.subtype _
  let g : (graphOfEdges S).support ↪ Fin n := e.toEquiv.toEmbedding.trans j
  obtain ⟨σ, hσ⟩ := exists_perm_comp_embedding f g
  have hfun : (fun v => σ (f v)) = (fun v => j (e v)) := funext hσ
  have hm : ((edgeSupportGraph S).map f).map σ.toEmbedding =
      (edgeSupportGraph T).map j := by
    rw [SimpleGraph.map_map]
    change (edgeSupportGraph S).map (fun v => σ (f v)) = _
    rw [hfun]
    change (edgeSupportGraph S).map (j ∘ e.toEquiv.toEmbedding) = _
    rw [← SimpleGraph.map_map, map_eq_of_iso]
  refine ⟨σ, (graphEdgeEquiv n).injective ?_⟩
  change graphOfEdges (σ • S) = graphOfEdges T
  rw [graphOfEdges_smul]
  simpa only [f, j, edgeSupportGraph_map] using hm

theorem subgraph_eq_edgeSubgraph
    (K : (⊤ : SimpleGraph (Fin n)).Subgraph)
    (hK : ∀ v : K.verts, ∃ w, K.coe.Adj v w) :
    K = edgeSubgraph (graphEdges K.spanningCoe) := by
  apply SimpleGraph.Subgraph.ext
  · change K.verts = (graphOfEdges (graphEdges K.spanningCoe)).support
    rw [graphOfEdges_graphEdges]
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw⟩ := hK ⟨v, hv⟩
      exact ⟨w, hw⟩
    · rintro ⟨w, hw⟩
      exact K.edge_vert hw
  · change K.Adj = (graphOfEdges (graphEdges K.spanningCoe)).Adj
    rw [graphOfEdges_graphEdges]
    rfl

theorem subgraph_eq_edgeSubgraph_of_iso {S : Finset (Edge n)}
    (K : (⊤ : SimpleGraph (Fin n)).Subgraph)
    (e : edgeSupportGraph S ≃g K.coe) :
    K = edgeSubgraph (graphEdges K.spanningCoe) := by
  apply subgraph_eq_edgeSubgraph K
  intro v
  obtain ⟨w, hw⟩ := edgeSupportGraph_noIsolates S (e.symm v)
  refine ⟨e w, ?_⟩
  have hh : K.coe.Adj (e (e.symm v)) (e w) := e.toHom.map_adj hw
  simpa only [e.apply_symm_apply] using hh

theorem edgeCount_edgeSupportGraph (S : Finset (Edge n)) :
    edgeCount (edgeSupportGraph S) = S.card := by
  classical
  have h := card_mappedGraphEdges
    (Function.Embedding.subtype (fun v => v ∈ (graphOfEdges S).support))
    (edgeSupportGraph S)
  simpa only [edgeSupportGraph_map, graphEdges_graphOfEdges] using h.symm

/-- A selected edge subset of an embedded graph pulls back to an actual copy
inside the original graph, using only incident vertices of the selection. -/
def edgeSupportGraph_copy_of_subset {V : Type*} (f : V ↪ Fin n)
    (H : SimpleGraph V) (S : Finset (Edge n))
    (hS : S ⊆ graphEdges (H.map f)) : (edgeSupportGraph S).Copy H := by
  have hle : graphOfEdges S ≤ H.map f := by
    simpa only [graphOfEdges_graphEdges] using graphOfEdges_mono hS
  have hrange (v : (graphOfEdges S).support) : ∃ a : V, f a = v.val := by
    obtain ⟨w, hw⟩ := v.property
    obtain ⟨a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj f H v w).mp (hle hw)
    exact ⟨a, ha⟩
  let g : (graphOfEdges S).support → V := fun v => Classical.choose (hrange v)
  have hg (v : (graphOfEdges S).support) : f (g v) = v.val :=
    Classical.choose_spec (hrange v)
  refine { toHom := ⟨g, ?_⟩, injective' := ?_ }
  · intro v w hvw
    apply (SimpleGraph.map_adj_apply (f := f)).mp
    rw [hg v, hg w]
    exact hle hvw
  · intro v w hvw
    change g v = g w at hvw
    apply Subtype.ext
    rw [← hg v, ← hg w, hvw]

theorem exists_subgraph_iso_edgeSupportGraph {V : Type*} (f : V ↪ Fin n)
    (H : SimpleGraph V) (S : Finset (Edge n))
    (hS : S ⊆ graphEdges (H.map f)) :
    ∃ F : H.Subgraph, Nonempty (edgeSupportGraph S ≃g F.coe) :=
  SimpleGraph.isContained_iff_exists_iso_subgraph.mp
    ⟨edgeSupportGraph_copy_of_subset f H S hS⟩

end LeanBlast.SecondKahnKalai

end

end OAI
