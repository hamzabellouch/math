import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.BirthGraph
import OAI.Combinatorics.TriangleRemoval.Process.BornEdges
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEmbeddings
import OAI.Combinatorics.TriangleRemoval.Process.LookupGraph

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N n : ℕ} (B : BirthGraph N) (G : Graph n)

lemma graph_edge_mem {i j : Fin N} (hij : B.graph.Adj i j) :
    ({i,j} : Finset (Fin N)) ∈ B.backEdges Finset.univ := by
  rcases hij with h | h
  · exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨i,h,rfl⟩⟩
  · rw [Finset.pair_comm]
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨j,h,rfl⟩⟩

noncomputable def initialAssignmentSet (k : ℕ) (hk : k ≤ N) :
    Finset ({x // x ∈ initialVertices N k} ↪ Fin n) := by
  classical
  exact (prefixEmbeddings B.graph (lookupGraph G) k hk).image initialSubtypeLabel

open Classical in

lemma initialAssignmentSet_card (k : ℕ) (hk : k ≤ N) :
    (B.initialAssignmentSet G k hk).card ≤
      (prefixEmbeddings B.graph (lookupGraph G) k hk).card := by
  classical
  exact Finset.card_image_le

theorem initialLabel_mem {a b : Fin N} {φ : Fin N ↪ Fin n}
    (hφ : φ ∈ graphEmbeddingSet
      (insert ({a,b} : Finset (Fin N)) (B.backEdges Finset.univ)) G)
    (k : ℕ) (hk : k ≤ N) :
    restrictLabel (initialVertices N k) φ ∈ B.initialAssignmentSet G k hk := by
  classical
  refine Finset.mem_image.mpr ⟨initialLabel hk φ,?_,initialSubtypeLabel_initialLabel hk φ⟩
  apply (mem_prefixEmbeddings _).mpr
  intro i j hij
  refine ⟨φ.injective.ne (B.graph.ne_of_adj hij),?_⟩
  have he := B.graph_edge_mem hij
  have hm := (Finset.mem_filter.mp hφ).2 (Finset.mem_image.mpr
    ⟨_,Finset.mem_insert_of_mem he,rfl⟩)
  change ({φ (Fin.castLE hk i), φ (Fin.castLE hk j)} : Finset (Fin n)) ∈ G
  simpa only [Finset.map_insert,Finset.map_singleton] using hm

theorem two_preceding_neighbors (R : ℕ)
    (hb : ∀ v : Fin N, R ≤ v.val → (B.older v).card = 2)
    (k : ℕ) (hR : R ≤ k) (hk : k+1 ≤ N) :
    ∃ u v : Fin k, u ≠ v ∧
      B.graph.Adj (Fin.castLE (by omega) u) ⟨k,by omega⟩ ∧
      B.graph.Adj (Fin.castLE (by omega) v) ⟨k,by omega⟩ := by
  obtain ⟨u,v,huv,he⟩ := Finset.card_eq_two.mp (hb ⟨k,by omega⟩ hR)
  have hu : u ∈ B.older ⟨k,by omega⟩ := by rw [he]; simp
  have hv : v ∈ B.older ⟨k,by omega⟩ := by rw [he]; simp
  have huk : u.val < k := B.older_lt _ u hu
  have hvk : v.val < k := B.older_lt _ v hv
  refine ⟨⟨u.val,huk⟩,⟨v.val,hvk⟩,?_,Or.inl hu,Or.inl hv⟩
  intro hh
  exact huv (Fin.ext (congrArg (fun z : Fin k => z.val) hh))

end SharpTerminalLeave.BirthGraph

end

end OAI
