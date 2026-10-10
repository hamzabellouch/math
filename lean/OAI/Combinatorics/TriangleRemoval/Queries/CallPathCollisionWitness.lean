import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.TriangleHypergraphLinear
import OAI.Combinatorics.TriangleRemoval.Process.LookupGraph
import OAI.Combinatorics.TriangleRemoval.Queries.RecordedCallForest
import OAI.Combinatorics.TriangleRemoval.Process.EdgeMatching
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth2
import OAI.Combinatorics.TriangleRemoval.Process.PathSuffix
import OAI.Combinatorics.TriangleRemoval.Queries.KeyCandidate

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

namespace RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)
variable (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G)

theorem call_path_collision_witness (i j : Fin F.size) (hne : i ≠ j) (T : Finset (Fin n))
    (hi : T ∈ (F.call i).keys (triangleHypergraph G))
    (hj : T ∈ (F.call j).keys (triangleHypergraph G)) :
    ∃ a b : Fin F.vertexCount,
      (F.toTriangleGrowth hM hG).birthGraph.ExtraEdge (lookupGraph G) F.vertexLabel a b ∧
      Set.InjOn F.vertexLabel ((F.toTriangleGrowth hM hG).pathUnion a b) := by
  let A := F.toTriangleGrowth hM hG
  obtain ⟨v,hv,hve⟩ := F.key_exposed hM hG i T hi
  obtain ⟨w,hw,hwe⟩ := F.key_exposed hM hG j T hj
  have hvw : v ≠ w := by
    rcases hv with ⟨hiv,hvr⟩ | ⟨hiv,rfl⟩ <;> rcases hw with ⟨hjw,hwr⟩ | ⟨hjw,rfl⟩
    · exact False.elim (hne (hiv.trans hjw.symm))
    · intro he
      have hh := F.birthIndex_nonroot j hjw
      rw [← he] at hh
      omega
    · intro he
      have hh := F.birthIndex_nonroot i hiv
      rw [he] at hh
      omega
    · exact fun he => hne (F.birthIndex_injective i j hiv hjw he)
  exact A.injective_path_collision hvw hve hwe

end RecordedCallForest

theorem traced_graph_path_collision_witness {n : ℕ} (G : Graph n) (N d k : ℕ)
    (c : QueryCall (Finset (Fin n)) (Finset (Fin n)))
    (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G)
    (hc : c.Separated (triangleHypergraph G))
    (ν : Finset (Fin n) → PMF (Fin N))
    (z : (Bool × List (QueryCall (Finset (Fin n)) (Finset (Fin n)))) × List (Finset (Fin n)))
    (hz : z ∈ (ExposureTree.freshLog ν
      (tracedGridQuery (triangleHypergraph G) N d k c)).support)
    (hr : ExposureTree.repeats ∅ z.2 = true) :
    let F := extractCallForest (triangleHypergraph G) N d k c ν z hz
    ∃ a b : Fin F.vertexCount,
      (F.toTriangleGrowth hM hG).birthGraph.ExtraEdge (lookupGraph G) F.vertexLabel a b ∧
      Set.InjOn F.vertexLabel ((F.toTriangleGrowth hM hG).pathUnion a b) := by
  let F := extractCallForest (triangleHypergraph G) N d k c ν z hz
  obtain ⟨a,ha,b,hb,hab,T,haT,hbT⟩ := graph_query_repeat_addresses G N d k c hc ν hz hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hb
  have hij : i ≠ j := fun he => hab (he ▸ rfl)
  exact F.call_path_collision_witness hM hG i j hij T haT hbT

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
