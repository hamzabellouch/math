import Mathlib
import OAI.Computability.VertexCover.Basic
import OAI.Computability.VertexCover.PCP.PreprocessingOverlayTables
import OAI.Computability.VertexCover.Analysis.GraphCompleteness

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.ExplicitGraph
noncomputable section

def materialize {V : Type*} [Fintype V] (G : SimpleGraph V) : ExplicitGraph := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let E : Finset (Fin (Fintype.card V) × Fin (Fintype.card V)) :=
    Finset.univ.filter (fun p => p.1 < p.2 ∧ G.Adj (e.symm p.1) (e.symm p.2))
  exact ⟨Fintype.card V, E.toList,
    fun p hp => (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2.1,
    E.nodup_toList⟩

 theorem materialize_n {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (materialize G).n = Fintype.card V := rfl

 theorem materialize_mem_edges {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v w : Fin (Fintype.card V)) :
    (v,w) ∈ (materialize G).edges ↔
      v < w ∧ G.Adj ((Fintype.equivFin V).symm v) ((Fintype.equivFin V).symm w) := by
  classical
  change (v,w) ∈ (Finset.univ.filter (fun p : Fin (Fintype.card V) × Fin (Fintype.card V) =>
    p.1 < p.2 ∧ G.Adj ((Fintype.equivFin V).symm p.1)
      ((Fintype.equivFin V).symm p.2))).toList ↔ _
  exact Finset.mem_toList.trans (by simp only [Finset.mem_filter, Finset.mem_univ, true_and])

 theorem coverNumber_le {G : ExplicitGraph} (C : Finset (Fin G.n)) (hC : G.Cover C) :
    G.coverNumber ≤ C.card := Nat.find_min' _ ⟨C,hC,rfl⟩

 theorem materialize_cover {V : Type*} [Fintype V] (G : SimpleGraph V)
    (C : Finset V) (hC : G.IsVertexCover (C : Set V)) :
    ∃ S : Finset (Fin (materialize G).n), (materialize G).Cover S ∧ S.card = C.card := by
  classical
  let e := Fintype.equivFin V
  refine ⟨C.map e.toEmbedding, ?_, Finset.card_map _⟩
  intro p hp
  have h := ((materialize_mem_edges G p.1 p.2).mp hp).2
  have hh := hC h
  rcases hh with hv | hw
  · left
    exact Finset.mem_map.mpr ⟨e.symm p.1, hv, e.apply_symm_apply _⟩
  · right
    exact Finset.mem_map.mpr ⟨e.symm p.2, hw, e.apply_symm_apply _⟩

 theorem materialize_coverNumber_lt {V : Type*} [Fintype V] (G : SimpleGraph V)
    (C : Finset V) (hC : G.IsVertexCover (C : Set V)) (ρ : ℝ)
    (hcard : (C.card : ℝ) < ρ * Fintype.card V) :
    ((materialize G).coverNumber : ℝ) < ρ * (materialize G).n := by
  obtain ⟨S, hS, hScard⟩ := materialize_cover G C hC
  have hle := coverNumber_le S hS
  rw [hScard] at hle
  exact (Nat.cast_le.mpr hle).trans_lt hcard

end
end VertexCover.ExplicitGraph

namespace VertexCover.LabelCover
noncomputable section

def explicitGraph (Φ : LabelCover) (m : ℕ) : ExplicitGraph :=
  ExplicitGraph.materialize (Φ.graph (Parameters.d m) (Parameters.t m))

 theorem explicitGraph_vertices (Φ : LabelCover) (m : ℕ) :
    (Φ.explicitGraph m).n = Φ.M^((Parameters.d m).choose 2) *
      (2*Parameters.d m+1)^(Φ.WeightDimension (Parameters.d m) * Parameters.d m) :=
  Φ.vertex_card _

 theorem explicitGraph_complete (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (A : Φ.Labeling) (hA : ∀ e, Φ.Satisfies A e) :
    ((Φ.explicitGraph m).coverNumber : ℝ) <
      ((1:ℝ)/2+1/(m:ℝ)) * (Φ.explicitGraph m).n := by
  obtain ⟨C, hC, hcard⟩ := Φ.graph_completeness_cover m hm A hA
  exact ExplicitGraph.materialize_coverNumber_lt _ C hC _ hcard

end
end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
