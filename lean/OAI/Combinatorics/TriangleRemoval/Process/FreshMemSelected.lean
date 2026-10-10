import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.TriangleThird
import OAI.Combinatorics.TriangleRemoval.Process.Attachment
import OAI.Combinatorics.TriangleRemoval.Process.EdgeMatching
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth2

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)
variable (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G)

lemma fresh_mem_selected {V : Type*} [DecidableEq V] {e a : Finset V} {x : V}
    (he : e.card = 2) (ha : a.card = 2) (hs : e ⊆ insert x a) (hne : e ≠ a) : x ∈ e := by
  by_contra hx
  have hh : e ⊆ a := by
    intro z hz
    exact (Finset.mem_insert.mp (hs hz)).resolve_left (fun he => hx (he ▸ hz))
  exact hne (Finset.eq_of_subset_of_card_le hh (by rw [he,ha]))

lemma pair_has_other {V : Type*} [DecidableEq V] {e : Finset V} (he : e.card = 2) (x : V) :
    ∃ z ∈ e, z ≠ x := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp he
  by_cases ha : a = x
  · exact ⟨b,by simp,ha ▸ hab.symm⟩
  · exact ⟨a,by simp,ha⟩

lemma candidate_nonroot_exposed (i : Fin F.size) (hi : i ≠ F.root)
    (p : Finset (Fin n) × Finset (Fin n))
    (hp : p ∈ gridCandidates (triangleHypergraph G) (F.call i).focus (F.call i).parent) :
    (F.toTriangleGrowth hM hG).birthGraph.ExposedAt (lookupGraph G) F.vertexLabel
      (F.birthIndex i hi) p.2 := by
  let A := F.toTriangleGrowth hM hG
  have hc := (graphCandidate_iff G _ _ _).mp hp
  have hf := hc.1
  rw [F.incoming_focus i hi] at hf
  obtain ⟨hediff,hepow⟩ := Finset.mem_erase.mp hf
  obtain ⟨hes,hec⟩ := Finset.mem_powersetCard.mp hepow
  have hes' : p.1 ⊆ insert (F.newVertex i hi) (F.incoming i hi).1 := by
    rw [← (F.newVertex_spec i hi).2]
    exact hes
  have hnew := fresh_mem_selected hec (F.incoming_card i hi) hes' hediff
  obtain ⟨z,hze,hzn⟩ := pair_has_other hec (F.newVertex i hi)
  have hza : z ∈ (F.incoming i hi).1 := (Finset.mem_insert.mp (hes' hze)).resolve_left hzn
  have hv := F.birthIndex_nonroot i hi
  have him : (A.older (F.birthIndex i hi)).image F.vertexLabel = (F.incoming i hi).1 := by
    have hh := ((A.older_invariants (F.birthIndex i hi)).2 hv).2.1
    change (A.older (F.birthIndex i hi)).image F.vertexLabel = F.attachment (F.birthIndex i hi) at hh
    exact hh.trans (F.attachment_birth i hi)
  have hfT := (Finset.mem_powersetCard.mp hc.2.2.1).1
  obtain ⟨u,hum,huz⟩ := Finset.mem_image.mp (him.symm ▸ hza)
  refine ⟨lookupGraph_triangle hc.2.1,⟨u,hum,?_,?_⟩,?_⟩
  · exact huz.symm ▸ hfT hze
  · rw [F.vertexLabel_birth]
    exact hfT hnew
  · intro _ heq
    have hpar := hc.2.2.2
    rw [F.incoming_parent i hi] at hpar
    apply hpar
    apply congrArg some
    have hh := A.parentType_eq (F.birthIndex i hi) hv
    change A.birthGraph.parentType F.vertexLabel (F.birthIndex i hi) =
      insert (F.vertexLabel (F.birthIndex i hi)) (F.attachment (F.birthIndex i hi)) at hh
    rw [F.vertexLabel_birth,F.attachment_birth,← (F.newVertex_spec i hi).2] at hh
    exact heq.trans hh

lemma candidate_root_exposed (p : Finset (Fin n) × Finset (Fin n))
    (hp : p ∈ gridCandidates (triangleHypergraph G) c.focus c.parent) :
    ∃ v : Fin F.vertexCount, v.val < F.rootCount ∧
      (F.toTriangleGrowth hM hG).birthGraph.ExposedAt (lookupGraph G) F.vertexLabel v p.2 := by
  let A := F.toTriangleGrowth hM hG
  have hc := (graphCandidate_iff G _ _ _).mp hp
  obtain ⟨x,y,hx,hy,hxy,he⟩ := matchingSeed_covers F.vertexLabel c.focus hM
    F.vertexLabel_injective_roots (F.vertexLabel_covers) p.1 hc.1
  have hB : A.birthGraph.graph.Adj x y := (A.root_graph hx hy).mpr hxy
  have hfT := (Finset.mem_powersetCard.mp hc.2.2.1).1
  have hxT : F.vertexLabel x ∈ p.2 := hfT (he ▸ by simp)
  have hyT : F.vertexLabel y ∈ p.2 := hfT (he ▸ by simp)
  have hsmall (v : Fin F.vertexCount) (hv : v.val < F.rootCount) : (A.older v).card ≤ 1 := by
    rw [A.older_eq_seed hv]
    exact A.seed_small v hv
  rcases lt_or_gt_of_ne hB.ne with hlt | hgt
  · refine ⟨y,hy,lookupGraph_triangle hc.2.1,⟨x,(A.birthGraph.graph_adj_of_lt hlt).mp hB,hxT,hyT⟩,?_⟩
    intro hc2 _
    have hh := hsmall y hy
    change (A.older y).card = 2 at hc2
    omega
  · refine ⟨x,hx,lookupGraph_triangle hc.2.1,⟨y,(A.birthGraph.graph_adj_of_lt hgt).mp hB.symm,hyT,hxT⟩,?_⟩
    intro hc2 _
    have hh := hsmall x hx
    change (A.older x).card = 2 at hc2
    omega

end SharpTerminalLeave.RecordedCallForest

end

end OAI
