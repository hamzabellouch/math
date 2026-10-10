import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.ActiveHypergraph
import OAI.Combinatorics.TriangleRemoval.Queries.GridCollision
import OAI.Combinatorics.TriangleRemoval.Queries.MessageCandidatesReindex

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem triangleHypergraph_reindex {n : ℕ} (G : Graph n) (T : ↥(triangles G)) :
    triangleHypergraph G (triangleEmbedding G T) =
      (activeHypergraph G T).map (edgeEmbedding G) := by
  rw [activeHypergraph_map]
  simp [triangleHypergraph, triangleEmbedding, T.property]

theorem triangleHypergraph_active {n : ℕ} (G : Graph n) (e : ↥G)
    (T : Finset (Fin n)) (he : edgeEmbedding G e ∈ triangleHypergraph G T) :
    ∃ T' : ↥(triangles G), triangleEmbedding G T' = T := by
  by_cases hT : T ∈ triangles G
  · exact ⟨⟨T, hT⟩, rfl⟩
  · simp [triangleHypergraph, hT] at he

theorem active_cavity_eq {n : ℕ} (G : Graph n) (e : ↥G)
    (p : Option ↥(triangles G)) (t : ℝ) :
    cavityLimit (triangleHypergraph G) e.val (p.map Subtype.val) t =
      cavityLimit (activeHypergraph G) e p t :=
  cavityLimit_reindex _ _ (edgeEmbedding G) (triangleEmbedding G)
    (triangleHypergraph_reindex G) (triangleHypergraph_active G) e p t

theorem active_graph_cavity_error {n : ℕ} (G : Graph n) (focus : Finset ↥G) :
    |focusSurvival G (focus.map (edgeEmbedding G)) -
      ∏ e ∈ focus, cavityLimit (activeHypergraph G) e none 1| ≤
      collisionCost (triangleHypergraph G) (focus.map (edgeEmbedding G)) none := by
  have hf : focus.map (edgeEmbedding G) ⊆ G := by
    intro e he
    obtain ⟨e', _, rfl⟩ := Finset.mem_map.mp he
    exact e'.property
  have hh := graph_cavity_error G (focus.map (edgeEmbedding G)) hf
  rw [Finset.prod_map] at hh
  convert hh using 1
  congr 2
  apply Finset.prod_congr rfl
  intro e _
  exact (active_cavity_eq G e none 1).symm

end SharpTerminalLeave

end

end OAI
