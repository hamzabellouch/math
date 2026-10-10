import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.TriangleHypergraphLinear
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth
import OAI.Combinatorics.TriangleRemoval.Process.LookupGraph
import OAI.Combinatorics.TriangleRemoval.Queries.RecordedCallForest
import OAI.Combinatorics.TriangleRemoval.Process.EdgeMatching
import OAI.Combinatorics.TriangleRemoval.Process.FreshMemSelected

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

lemma QueryCall.key_has_candidate {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]
    (H : τ → Finset ι) (c : QueryCall ι τ) (T : τ) (h : T ∈ c.keys H) :
    ∃ e, (e,T) ∈ gridCandidates H c.focus c.parent := by
  obtain ⟨p,hp,he⟩ := List.mem_map.mp h
  exact ⟨p.1,he ▸ Finset.mem_toList.mp hp⟩

namespace RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)
variable (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G)

lemma key_exposed (i : Fin F.size) (T : Finset (Fin n))
    (hT : T ∈ (F.call i).keys (triangleHypergraph G)) :
    ∃ v : Fin F.vertexCount,
      ((i = F.root ∧ v.val < F.rootCount) ∨ (∃ hi : i ≠ F.root, v = F.birthIndex i hi)) ∧
      (F.toTriangleGrowth hM hG).birthGraph.ExposedAt (lookupGraph G) F.vertexLabel v T := by
  obtain ⟨e,he⟩ := (F.call i).key_has_candidate (triangleHypergraph G) T hT
  by_cases hi : i = F.root
  · subst i
    rw [F.root_eq] at he
    obtain ⟨v,hv,hve⟩ := F.candidate_root_exposed hM hG (e,T) he
    exact ⟨v,Or.inl ⟨rfl,hv⟩,hve⟩
  · exact ⟨F.birthIndex i hi,Or.inr ⟨hi,rfl⟩,F.candidate_nonroot_exposed hM hG i hi (e,T) he⟩

theorem call_collision_witness (i j : Fin F.size) (hne : i ≠ j) (T : Finset (Fin n))
    (hi : T ∈ (F.call i).keys (triangleHypergraph G))
    (hj : T ∈ (F.call j).keys (triangleHypergraph G)) :
    ∃ S : Set (Fin F.vertexCount), IsLowerSet S ∧ Set.InjOn F.vertexLabel S ∧
      ∃ a ∈ S, ∃ b ∈ S,
        (F.toTriangleGrowth hM hG).birthGraph.ExtraEdge (lookupGraph G) F.vertexLabel a b := by
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
  exact A.birthGraph.exposed_collision_witness (lookupGraph G) F.vertexLabel A.spawnRules
    F.rootCount F.vertexLabel_injective_roots
    (fun v hv => ((A.older_invariants v).2 hv).1) hvw hve hwe

end RecordedCallForest

theorem traced_graph_collision_witness {n : ℕ} (G : Graph n) (N d k : ℕ)
    (c : QueryCall (Finset (Fin n)) (Finset (Fin n)))
    (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G)
    (hc : c.Separated (triangleHypergraph G))
    (ν : Finset (Fin n) → PMF (Fin N))
    (z : (Bool × List (QueryCall (Finset (Fin n)) (Finset (Fin n)))) × List (Finset (Fin n)))
    (hz : z ∈ (ExposureTree.freshLog ν
      (tracedGridQuery (triangleHypergraph G) N d k c)).support)
    (hr : ExposureTree.repeats ∅ z.2 = true) :
    let F := extractCallForest (triangleHypergraph G) N d k c ν z hz
    ∃ S : Set (Fin F.vertexCount), IsLowerSet S ∧ Set.InjOn F.vertexLabel S ∧
      ∃ a ∈ S, ∃ b ∈ S,
        (F.toTriangleGrowth hM hG).birthGraph.ExtraEdge (lookupGraph G) F.vertexLabel a b := by
  let F := extractCallForest (triangleHypergraph G) N d k c ν z hz
  obtain ⟨a,ha,b,hb,hab,T,haT,hbT⟩ := graph_query_repeat_addresses G N d k c hc ν hz hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hb
  have hij : i ≠ j := fun he => hab (he ▸ rfl)
  exact F.call_collision_witness hM hG i j hij T haT hbT

end SharpTerminalLeave

end

end OAI
