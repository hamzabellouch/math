import OAI.Combinatorics.GraphThreshold.GraphEncoding
import OAI.Combinatorics.GraphThreshold.FiniteProbability

namespace OAI

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

universe u

variable {n : ℕ} {V : Type u}

/-- Regard an actual subgraph as a subgraph of the complete graph. Its vertex set,
including all isolated vertices, is unchanged. -/
def subgraphToComplete {G : SimpleGraph (Fin n)} (K : G.Subgraph) :
    (⊤ : SimpleGraph (Fin n)).Subgraph where
  verts := K.verts
  Adj := K.Adj
  adj_sub h := h.ne
  edge_vert := K.edge_vert
  symm := K.symm

/-- A complete-graph subgraph whose edges occur in G is the same actual subgraph of G. -/
def subgraphFromComplete (G : SimpleGraph (Fin n))
    (K : (⊤ : SimpleGraph (Fin n)).Subgraph) (hK : K.spanningCoe ≤ G) :
    G.Subgraph where
  verts := K.verts
  Adj := K.Adj
  adj_sub h := hK h
  edge_vert := K.edge_vert
  symm := K.symm

/-- Copies are put in bijection without choosing or counting graph embeddings. -/
def completeCopyEquiv (G : SimpleGraph (Fin n)) (F : SimpleGraph V) :
    {K : G.Subgraph // Nonempty (F ≃g K.coe)} ≃
      {K : (⊤ : SimpleGraph (Fin n)).Subgraph //
        Nonempty (F ≃g K.coe) ∧ K.spanningCoe ≤ G} where
  toFun K := ⟨subgraphToComplete K.val, K.property, fun _ _ h => K.val.adj_sub h⟩
  invFun K := ⟨subgraphFromComplete G K.val K.property.2, K.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem copyCount_eq_complete_card (G : SimpleGraph (Fin n)) (F : SimpleGraph V) :
    G.copyCount F = Nat.card
      {K : (⊤ : SimpleGraph (Fin n)).Subgraph //
        Nonempty (F ≃g K.coe) ∧ K.spanningCoe ≤ G} := by
  classical
  calc
    G.copyCount F = Fintype.card {K : G.Subgraph // Nonempty (F ≃g K.coe)} := by
      rw [SimpleGraph.copyCount, Fintype.card_subtype]
      apply congrArg Finset.card
      ext K
      simp
    _ = Fintype.card {K : (⊤ : SimpleGraph (Fin n)).Subgraph //
        Nonempty (F ≃g K.coe) ∧ K.spanningCoe ≤ G} :=
      Fintype.card_congr (completeCopyEquiv G F)
    _ = _ := Nat.card_eq_fintype_card.symm

theorem copyCount_eq_sum_complete (G : SimpleGraph (Fin n)) (F : SimpleGraph V) :
    (G.copyCount F : ℝ) =
      ∑ K : (⊤ : SimpleGraph (Fin n)).Subgraph,
        if Nonempty (F ≃g K.coe) then (if K.spanningCoe ≤ G then (1 : ℝ) else 0)
        else 0 := by
  classical
  rw [copyCount_eq_complete_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro K _
  by_cases hF : Nonempty (F ≃g K.coe) <;> simp [hF]

/-- Adding ambient isolated vertices does not change the edge count. -/
theorem edgeCount_spanningCoe {G : SimpleGraph (Fin n)} (K : G.Subgraph) :
    edgeCount K.spanningCoe = edgeCount K.coe := by
  unfold edgeCount
  rw [SimpleGraph.Subgraph.edgeSet_spanningCoe, ← K.image_coe_edgeSet_coe]
  exact Nat.card_congr
    (Equiv.Set.image (Sym2.map (Subtype.val : K.verts → Fin n)) K.coe.edgeSet
      (Sym2.map.injective Subtype.val_injective)).symm

theorem card_graphEdges_of_copy (F : SimpleGraph V)
    (K : (⊤ : SimpleGraph (Fin n)).Subgraph) (hK : Nonempty (F ≃g K.coe)) :
    (graphEdges K.spanningCoe).card = edgeCount F := by
  obtain ⟨f⟩ := hK
  rw [card_graphEdges, edgeCount_spanningCoe]
  exact (Nat.card_congr f.mapEdgeSet).symm

theorem subgraph_survival_probability (p : ℝ)
    (K : (⊤ : SimpleGraph (Fin n)).Subgraph) :
    bernoulliProbability p (fun W : Finset (Edge n) =>
      K.spanningCoe ≤ graphOfEdges W) = p ^ edgeCount K.coe := by
  have h : ∀ W : Finset (Edge n),
      K.spanningCoe ≤ graphOfEdges W ↔ graphEdges K.spanningCoe ⊆ W := by
    intro W
    calc
      K.spanningCoe ≤ graphOfEdges W ↔
          graphOfEdges (graphEdges K.spanningCoe) ≤ graphOfEdges W := by
        rw [graphOfEdges_graphEdges]
      _ ↔ graphEdges K.spanningCoe ⊆ W := graphOfEdges_le_iff
  simp_rw [h]
  rw [bernoulliProbability_subset, card_graphEdges, edgeCount_spanningCoe]

/-- The exact expected number of unlabelled, non-induced copies. The counted
objects include their vertex sets, so the identity retains isolated vertices. -/
theorem expectedCopies_formula (n : ℕ) (p : ℝ) (F : SimpleGraph V) :
    expectedCopies n p F =
      ((⊤ : SimpleGraph (Fin n)).copyCount F : ℝ) * p ^ edgeCount F := by
  classical
  calc
    expectedCopies n p F =
        ∑ K : (⊤ : SimpleGraph (Fin n)).Subgraph,
          if Nonempty (F ≃g K.coe) then p ^ edgeCount F else 0 := by
      unfold expectedCopies bernoulliExpectation
      simp_rw [copyCount_eq_sum_complete, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro K _
      by_cases hK : Nonempty (F ≃g K.coe)
      · simp only [hK, ite_true]
        have hsurv := subgraph_survival_probability p K
        have hedge : edgeCount K.coe = edgeCount F :=
          (Nat.card_congr hK.some.mapEdgeSet).symm
        rw [hedge] at hsurv
        rw [← hsurv]
        unfold bernoulliProbability
        apply Finset.sum_congr rfl
        intro W _
        by_cases hW : K.spanningCoe ≤ graphOfEdges W <;> simp [hW]
      · simp [hK]
    _ = ((⊤ : SimpleGraph (Fin n)).copyCount F : ℝ) * p ^ edgeCount F := by
      rw [copyCount_eq_sum_complete, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro K _
      by_cases hK : Nonempty (F ≃g K.coe) <;> simp [hK]

end LeanBlast.SecondKahnKalai

end

end OAI
