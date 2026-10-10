import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.TerminalLaw

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def activeHypergraph {n : ℕ} (G : Graph n) (T : ↥(triangles G)) : Finset ↥G :=
  Finset.univ.filter (fun e => e.val ∈ T.val.powersetCard 2)

def edgeEmbedding {n : ℕ} (G : Graph n) : ↥G ↪ Finset (Fin n) :=
  ⟨Subtype.val, Subtype.val_injective⟩

def triangleEmbedding {n : ℕ} (G : Graph n) : ↥(triangles G) ↪ Finset (Fin n) :=
  ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem activeHypergraph_mem {n : ℕ} (G : Graph n)
    (T : ↥(triangles G)) (e : ↥G) : e ∈ activeHypergraph G T ↔ e.val ∈ T.val.powersetCard 2 := by
  simp only [activeHypergraph, Finset.mem_filter, Finset.mem_univ, true_and]

theorem activeHypergraph_map {n : ℕ} (G : Graph n) (T : ↥(triangles G)) :
    (activeHypergraph G T).map (edgeEmbedding G) = T.val.powersetCard 2 := by
  ext e
  simp only [Finset.mem_map, activeHypergraph_mem, edgeEmbedding, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf
  · intro he
    exact ⟨⟨e, (mem_triangles.mp T.property).2 he⟩, he, rfl⟩

@[simp] theorem activeHypergraph_card {n : ℕ} (G : Graph n) (T : ↥(triangles G)) :
    (activeHypergraph G T).card = 3 := by
  have hh := congrArg Finset.card (activeHypergraph_map G T)
  simpa only [Finset.card_map, triangle_edge_card T.property] using hh

end SharpTerminalLeave

end

end OAI
