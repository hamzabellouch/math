import OAI.Combinatorics.GraphThreshold.GraphEncoding
import OAI.Combinatorics.GraphThreshold.EmbeddingExtension

namespace OAI

noncomputable section

open scoped Pointwise

namespace LeanBlast.SecondKahnKalai

variable {n : ℕ} {V : Type*}

theorem card_mappedGraphEdges [Fintype V] (f : V ↪ Fin n) (H : SimpleGraph V) :
    (graphEdges (H.map f)).card = edgeCount H := by
  classical
  rw [card_graphEdges, edgeCount_eq_card_edgeFinset, edgeCount_eq_card_edgeFinset]
  exact SimpleGraph.card_edgeFinset_map f H

theorem mapped_copy_le {U W : Type*} {H : SimpleGraph U} {G : SimpleGraph W}
    (c : H.Copy G) : H.map c.toEmbedding ≤ G := by
  intro a b hab
  obtain ⟨v, w, hvw, rfl, rfl⟩ := (SimpleGraph.map_adj c.toEmbedding H a b).mp hab
  exact c.toHom.map_adj hvw

/-- Containment of a graph is equivalent to containing a permuted copy of its
edges. The embedding carries *all* vertices, so isolated vertices are retained. -/
theorem isContained_iff_exists_smul_subset (f : V ↪ Fin n) (H : SimpleGraph V)
    (W : Finset (Edge n)) :
    H.IsContained (graphOfEdges W) ↔
      ∃ σ : Equiv.Perm (Fin n), σ • graphEdges (H.map f) ⊆ W := by
  constructor
  · rintro ⟨c⟩
    obtain ⟨σ, hσ⟩ := exists_perm_comp_embedding f c.toEmbedding
    refine ⟨σ, graphOfEdges_le_iff.mp ?_⟩
    rw [graphOfEdges_smul, graphOfEdges_graphEdges, SimpleGraph.map_map]
    have heq : (fun v => σ.toEmbedding (f v)) = c.toEmbedding := by
      funext v
      exact hσ v
    change H.map (fun v => σ.toEmbedding (f v)) ≤ graphOfEdges W
    rw [heq]
    exact mapped_copy_le c
  · rintro ⟨σ, hσ⟩
    have hf : H.IsContained (H.map f) :=
      ⟨(SimpleGraph.Embedding.map f H).toCopy⟩
    have hperm : (H.map f).IsContained (graphOfEdges (σ • graphEdges (H.map f))) := by
      rw [graphOfEdges_smul, graphOfEdges_graphEdges]
      exact ⟨(SimpleGraph.Iso.map σ _).toCopy⟩
    exact hf.trans (hperm.trans (SimpleGraph.IsContained.of_le (graphOfEdges_mono hσ)))

theorem copyCount_pos_iff_exists_smul_subset (f : V ↪ Fin n) (H : SimpleGraph V)
    (W : Finset (Edge n)) :
    0 < (graphOfEdges W).copyCount H ↔
      ∃ σ : Equiv.Perm (Fin n), σ • graphEdges (H.map f) ⊆ W :=
  SimpleGraph.copyCount_pos.trans (isContained_iff_exists_smul_subset f H W)

theorem exists_graphRepresentation [Fintype V] (n : ℕ) (H : SimpleGraph V)
    (hcard : Fintype.card V ≤ n) :
    ∃ E : Finset (Edge n), E.card = edgeCount H ∧
      ∀ W : Finset (Edge n),
        (0 < (graphOfEdges W).copyCount H ↔
          ∃ σ : Equiv.Perm (Fin n), σ • E ⊆ W) := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card V ≤ Fintype.card (Fin n) by simpa using hcard)
  exact ⟨graphEdges (H.map f), card_mappedGraphEdges f H,
    copyCount_pos_iff_exists_smul_subset f H⟩

end LeanBlast.SecondKahnKalai

end

end OAI
