import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth2
import OAI.Combinatorics.TriangleRemoval.Process.TriangleHypergraph
import OAI.Combinatorics.TriangleRemoval.Process.BornEdges
import OAI.Combinatorics.TriangleRemoval.Queries.RecordedCallForest
import OAI.Combinatorics.TriangleRemoval.Process.EdgeMatching

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

section MatchingSeedEdgeCount
variable {V : Type*} [DecidableEq V] {N R : ℕ}
variable (label : Fin N → V) (E : Finset (Finset V)) (hE : EdgeMatching E)
variable (hi : Set.InjOn label {v | v.val < R})

lemma matchingSeed_edge_roots (Z : Finset (Fin N)) {e : Finset (Fin N)}
    (he : e ∈ (matchingSeed label E hE hi).backEdges Z) :
    ∀ x ∈ e, x.val < R := by
  obtain ⟨v,_,u,hu,rfl⟩ := BirthGraph.backEdges_mem_pair _ he
  obtain ⟨hv,huv,_⟩ := (matchingSeed_mem_older label E hE hi v u).mp hu
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact lt_trans huv hv
  · simpa only [Finset.mem_singleton] using (Finset.mem_singleton.mp hx ▸ hv)

lemma matchingSeed_edge_image (Z : Finset (Fin N)) {e : Finset (Fin N)}
    (he : e ∈ (matchingSeed label E hE hi).backEdges Z) : e.image label ∈ E := by
  obtain ⟨v,_,u,hu,rfl⟩ := BirthGraph.backEdges_mem_pair _ he
  simpa only [Finset.image_insert,Finset.image_singleton] using
    ((matchingSeed_mem_older label E hE hi v u).mp hu).2.2

theorem matchingSeed_edge_count (Z : Finset (Fin N)) :
    ((matchingSeed label E hE hi).backEdges Z).card ≤ E.card := by
  classical
  let S := (matchingSeed label E hE hi).backEdges Z
  have hinj : Set.InjOn (Finset.image label) S := by
    intro e he f hf hEq
    have heR := matchingSeed_edge_roots label E hE hi Z he
    have hfR := matchingSeed_edge_roots label E hE hi Z hf
    apply Finset.Subset.antisymm
    · intro x hx
      have hxI : label x ∈ f.image label := hEq ▸ Finset.mem_image_of_mem label hx
      obtain ⟨y,hy,hxy⟩ := Finset.mem_image.mp hxI
      exact hi (hfR y hy) (heR x hx) hxy ▸ hy
    · intro y hy
      have hyI : label y ∈ e.image label := hEq.symm ▸ Finset.mem_image_of_mem label hy
      obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp hyI
      exact hi (heR x hx) (hfR y hy) hxy ▸ hx
  rw [← Finset.card_image_of_injOn hinj]
  apply Finset.card_le_card
  intro e he
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
  exact matchingSeed_edge_image label E hE hi Z hf

end MatchingSeedEdgeCount

namespace RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

lemma growth_seed_count (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G) :
    ((F.toTriangleGrowth hM hG).seed.backEdges (F.toTriangleGrowth hM hG).roots).card ≤
      c.focus.card :=
  matchingSeed_edge_count F.vertexLabel c.focus hM F.vertexLabel_injective_roots _

end RecordedCallForest
end SharpTerminalLeave

end

end OAI
