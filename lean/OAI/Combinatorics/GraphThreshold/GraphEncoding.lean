import OAI.Combinatorics.GraphThreshold.Statement
import Mathlib.Algebra.Group.Action.Pointwise.Finset

namespace OAI

noncomputable section

open scoped Pointwise

namespace LeanBlast.SecondKahnKalai

/-- The non-loop edge set of an ordinary graph on `Fin n`. -/
def graphEdges {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Edge n) := by
  classical
  exact Finset.univ.filter (fun e => e.val ∈ G.edgeSet)

variable {n : ℕ}

/-- Vertex permutations act on unordered non-loop edges. -/
instance edgeMulAction : MulAction (Equiv.Perm (Fin n)) (Edge n) where
  smul σ e := ⟨Sym2.map σ e.val, fun h =>
    e.property ((Sym2.isDiag_map σ.injective).mp h)⟩
  one_smul e := by
    apply Subtype.ext
    change Sym2.map (1 : Equiv.Perm (Fin n)) e.val = e.val
    simp
  mul_smul σ τ e := by
    apply Subtype.ext
    change Sym2.map (σ * τ) e.val = Sym2.map σ (Sym2.map τ e.val)
    rw [Sym2.map_map]
    rfl

@[simp]
theorem edge_smul_val (σ : Equiv.Perm (Fin n)) (e : Edge n) :
    (σ • e).val = Sym2.map σ e.val := rfl

@[simp]
theorem mem_graphEdges (G : SimpleGraph (Fin n)) (e : Edge n) :
    e ∈ graphEdges G ↔ e.val ∈ G.edgeSet := by
  classical
  simp [graphEdges]

theorem edgeSet_graphOfEdges (W : Finset (Edge n)) :
    (graphOfEdges W).edgeSet = Subtype.val '' (W : Set (Edge n)) := by
  rw [graphOfEdges, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact And.left
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, a.property⟩

@[simp]
theorem mem_edgeSet_graphOfEdges (W : Finset (Edge n)) (e : Edge n) :
    e.val ∈ (graphOfEdges W).edgeSet ↔ e ∈ W := by
  classical
  simp [graphOfEdges, e.property, Subtype.val_injective.eq_iff]

@[simp]
theorem graphEdges_graphOfEdges (W : Finset (Edge n)) :
    graphEdges (graphOfEdges W) = W := by
  classical
  ext e
  simp

@[simp]
theorem graphOfEdges_graphEdges (G : SimpleGraph (Fin n)) :
    graphOfEdges (graphEdges G) = G := by
  apply SimpleGraph.edgeSet_injective
  ext e
  by_cases he : e.IsDiag
  · simp [SimpleGraph.not_mem_edgeSet_of_isDiag, he]
  · exact (mem_edgeSet_graphOfEdges (graphEdges G) ⟨e, he⟩).trans
      (mem_graphEdges G ⟨e, he⟩)

/-- No graphs or edge sets are omitted or multiply represented. -/
def graphEdgeEquiv (n : ℕ) : Finset (Edge n) ≃ SimpleGraph (Fin n) where
  toFun := graphOfEdges
  invFun := graphEdges
  left_inv := graphEdges_graphOfEdges
  right_inv := graphOfEdges_graphEdges

theorem graphOfEdges_smul (σ : Equiv.Perm (Fin n)) (W : Finset (Edge n)) :
    graphOfEdges (σ • W) = (graphOfEdges W).map σ.toEmbedding := by
  apply SimpleGraph.edgeSet_injective
  rw [edgeSet_graphOfEdges, SimpleGraph.edgeSet_map, edgeSet_graphOfEdges,
    Finset.smul_finset_def, Finset.coe_image, Set.image_image, Set.image_image]
  rfl

theorem graphEdges_map (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    graphEdges (G.map σ.toEmbedding) = σ • graphEdges G := by
  apply (graphEdgeEquiv n).injective
  change graphOfEdges _ = graphOfEdges _
  rw [graphOfEdges_graphEdges, graphOfEdges_smul, graphOfEdges_graphEdges]

@[simp]
theorem graphOfEdges_empty : graphOfEdges (∅ : Finset (Edge n)) = ⊥ := by
  simp [graphOfEdges]

@[simp]
theorem graphEdges_bot : graphEdges (⊥ : SimpleGraph (Fin n)) = ∅ := by
  classical
  ext e
  simp

@[simp]
theorem graphEdges_top : graphEdges (⊤ : SimpleGraph (Fin n)) = Finset.univ := by
  classical
  ext e
  simp [e.property]

@[simp]
theorem graphOfEdges_univ : graphOfEdges (Finset.univ : Finset (Edge n)) = ⊤ := by
  rw [← graphEdges_top, graphOfEdges_graphEdges]

theorem graphEdges_mono {G H : SimpleGraph (Fin n)} (h : G ≤ H) :
    graphEdges G ⊆ graphEdges H := by
  intro e he
  exact (mem_graphEdges H e).mpr (SimpleGraph.edgeSet_mono h
    ((mem_graphEdges G e).mp he))

theorem graphOfEdges_mono {S T : Finset (Edge n)} (h : S ⊆ T) :
    graphOfEdges S ≤ graphOfEdges T := by
  apply SimpleGraph.fromEdgeSet_mono
  exact Set.image_mono h

@[simp]
theorem graphOfEdges_le_iff {S T : Finset (Edge n)} :
    graphOfEdges S ≤ graphOfEdges T ↔ S ⊆ T := by
  constructor
  · intro h
    simpa using graphEdges_mono h
  · exact graphOfEdges_mono

/-- Edge-set encoding preserves the ordinary unlabelled edge count. -/
def graphEdgesEquiv (G : SimpleGraph (Fin n)) : ↥(graphEdges G) ≃ G.edgeSet where
  toFun e := ⟨e.val.val, (mem_graphEdges G e.val).mp e.property⟩
  invFun e := ⟨⟨e.val, G.not_isDiag_of_mem_edgeSet e.property⟩,
    (mem_graphEdges G _).mpr e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem card_graphEdges (G : SimpleGraph (Fin n)) :
    (graphEdges G).card = edgeCount G := by
  classical
  rw [edgeCount, Nat.card_eq_fintype_card, ← Fintype.card_coe]
  exact Fintype.card_congr (graphEdgesEquiv G)

@[simp]
theorem edgeCount_graphOfEdges (W : Finset (Edge n)) :
    edgeCount (graphOfEdges W) = W.card := by
  rw [← card_graphEdges, graphEdges_graphOfEdges]

theorem edgeCount_eq_card_edgeFinset {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    edgeCount G = G.edgeFinset.card := by
  classical
  rw [edgeCount, Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]

theorem edgeCount_eq_zero_iff {V : Type*} [Fintype V] (G : SimpleGraph V) :
    edgeCount G = 0 ↔ G = ⊥ := by
  classical
  rw [edgeCount_eq_card_edgeFinset, Finset.card_eq_zero]
  exact G.edgeFinset_eq_empty

theorem positive_copies_iff {V : Type*} (W : Finset (Edge n)) (H : SimpleGraph V) :
    0 < (graphOfEdges W).copyCount H ↔ H.IsContained (graphOfEdges W) :=
  SimpleGraph.copyCount_pos

end LeanBlast.SecondKahnKalai

end

end OAI
