import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth
import OAI.Combinatorics.TriangleRemoval.Process.RootSet
import OAI.Combinatorics.TriangleRemoval.Process.MatchingSeedEdgeRoots

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

theorem matchingSeed_full_edge_count {V : Type*} [DecidableEq V] {N R : ℕ}
    (label : Fin N → V) (E : Finset (Finset V)) (hE : EdgeMatching E)
    (hi : Set.InjOn label {v | v.val < R})
    (hc : ∀ e ∈ E, ∀ x ∈ e, ∃ v : Fin N, v.val < R ∧ label v = x) :
    ((matchingSeed label E hE hi).backEdges (Finset.univ.filter (fun v => v.val < R))).card = E.card := by
  classical
  apply Nat.le_antisymm (matchingSeed_edge_count label E hE hi _)
  let S := (matchingSeed label E hE hi).backEdges (Finset.univ.filter (fun v => v.val < R))
  have hsub : E ⊆ S.image (Finset.image label) := by
    intro e he
    obtain ⟨x,y,hx,hy,hxy,rfl⟩ := matchingSeed_covers label E hE hi hc e he
    have hp : ({x,y} : Finset (Fin N)) ∈ S := by
      rcases hxy with hxy | hyx
      · exact Finset.mem_biUnion.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩,
          Finset.mem_image.mpr ⟨x,hxy,rfl⟩⟩
      · have hh : ({y,x} : Finset (Fin N)) ∈ S := Finset.mem_biUnion.mpr
          ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,Finset.mem_image.mpr ⟨y,hyx,rfl⟩⟩
        simpa only [Finset.pair_comm] using hh
    exact Finset.mem_image.mpr ⟨{x,y},hp,by simp only [Finset.image_insert,Finset.image_singleton]⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

namespace RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

lemma growth_seed_card (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G) :
    ((F.toTriangleGrowth hM hG).seed.backEdges (F.toTriangleGrowth hM hG).roots).card = c.focus.card :=
  matchingSeed_full_edge_count F.vertexLabel c.focus hM F.vertexLabel_injective_roots F.vertexLabel_covers

lemma rootCount_focus_card (hM : EdgeMatching c.focus) : F.rootCount = 2*c.focus.card := by
  classical
  rw [rootCount,rootSet,Finset.card_biUnion]
  · calc
      ∑ e ∈ c.focus, e.card = ∑ _e ∈ c.focus, 2 := Finset.sum_congr rfl (fun e he => hM.1 e he)
      _ = 2*c.focus.card := by simp only [Finset.sum_const,smul_eq_mul,Nat.mul_comm]
  · exact hM.2

end RecordedCallForest
end SharpTerminalLeave

open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
