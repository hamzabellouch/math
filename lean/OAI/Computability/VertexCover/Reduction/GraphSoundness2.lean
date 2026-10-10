import Mathlib
import OAI.Computability.VertexCover.Reduction.Soundness
import OAI.Computability.VertexCover.Reduction.GraphSoundness

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

theorem coverNumber_witness (G : ExplicitGraph) :
    ∃ S : Finset (Fin G.n), G.Cover S ∧ S.card = G.coverNumber := by
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin G.n), G.Cover S ∧ S.card = k :=
    ⟨G.n, Finset.univ, by simp [Cover], by simp⟩
  exact Nat.find_spec hex

theorem materialize_cover_reflects {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset (Fin (materialize G).n)) (hS : (materialize G).Cover S) :
    ∃ C : Finset V, G.IsVertexCover (C : Set V) ∧ C.card = S.card := by
  classical
  let e := Fintype.equivFin V
  let C := S.map e.symm.toEmbedding
  have hmem (v : V) : v ∈ C ↔ e v ∈ S := by
    exact Finset.mem_map_equiv
  refine ⟨C, ?_, Finset.card_map _⟩
  intro v w hvw
  have hne : e v ≠ e w := fun he => G.ne_of_adj hvw (e.injective he)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hp := hS (e v, e w) ((materialize_mem_edges G (e v) (e w)).mpr
      ⟨hlt, by simpa only [e, Equiv.symm_apply_apply] using hvw⟩)
    exact hp.imp (hmem v).mpr (hmem w).mpr
  · have hp := hS (e w, e v) ((materialize_mem_edges G (e w) (e v)).mpr
      ⟨hgt, by simpa only [e, Equiv.symm_apply_apply] using hvw.symm⟩)
    exact hp.symm.imp (hmem v).mpr (hmem w).mpr

theorem materialize_coverNumber_gt {V : Type*} [Fintype V] (G : SimpleGraph V)
    (ρ : ℝ) (h : ∀ C : Finset V, G.IsVertexCover (C : Set V) →
      ρ * Fintype.card V < (C.card:ℝ)) :
    ρ * (materialize G).n < ((materialize G).coverNumber:ℝ) := by
  obtain ⟨S, hS, hmin⟩ := coverNumber_witness (materialize G)
  obtain ⟨C, hC, hcard⟩ := materialize_cover_reflects G S hS
  have hc := h C hC
  rw [hcard, hmin] at hc
  exact hc

end VertexCover.ExplicitGraph

namespace VertexCover.LabelCover

theorem explicitGraph_sound (Φ : LabelCover) (m : ℕ) (hm : 4 ≤ m)
    (hval : Φ.value ≤ Parameters.σ m) :
    (1-1/(m:ℝ))*(Φ.explicitGraph m).n < ((Φ.explicitGraph m).coverNumber:ℝ) := by
  exact ExplicitGraph.materialize_coverNumber_gt _ _ (Φ.graph_soundness_cover m hm hval)

end VertexCover.LabelCover

namespace VertexCover
noncomputable section

theorem rawGraph_soundness (m : ℕ) (hm : 4 ≤ m) (input : List Bool)
    (h : ¬ ThreeSAT input) :
    (1 - 1 / (m : ℝ)) * (rawGraph m hm input).n <
      ((rawGraph m hm input).coverNumber : ℝ) := by
  exact LabelCover.explicitGraph_sound _ m hm
    (le_of_lt (rawLabelCover_soundness m hm input h))

end
end VertexCover
end

section
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
