import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.MatchingSeedEdgeRoots
import OAI.Combinatorics.TriangleRemoval.Process.WitnessDimensions

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma matchingSeed_full_image {V : Type*} [DecidableEq V] {N R : ℕ}
    (label : Fin N → V) (E : Finset (Finset V)) (hE : EdgeMatching E)
    (hi : Set.InjOn label {v | v.val < R})
    (hc : ∀ e ∈ E, ∀ x ∈ e, ∃ v : Fin N, v.val < R ∧ label v = x) :
    ((matchingSeed label E hE hi).backEdges (Finset.univ.filter (fun v => v.val < R))).image
      (Finset.image label) = E := by
  classical
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact matchingSeed_edge_image label E hE hi _ hf
  · intro e he
    obtain ⟨x,y,hx,hy,hxy,rfl⟩ := matchingSeed_covers label E hE hi hc e he
    have hp : ({x,y} : Finset (Fin N)) ∈
        (matchingSeed label E hE hi).backEdges (Finset.univ.filter (fun v => v.val < R)) := by
      rcases hxy with hxy | hyx
      · exact Finset.mem_biUnion.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩,
          Finset.mem_image.mpr ⟨x,hxy,rfl⟩⟩
      · have hh : ({y,x} : Finset (Fin N)) ∈
            (matchingSeed label E hE hi).backEdges (Finset.univ.filter (fun v => v.val < R)) :=
          Finset.mem_biUnion.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,
            Finset.mem_image.mpr ⟨y,hyx,rfl⟩⟩
        simpa only [Finset.pair_comm] using hh
    exact Finset.mem_image.mpr ⟨{x,y},hp,by simp only [Finset.image_insert,Finset.image_singleton]⟩

namespace TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

lemma pathRootEdges_image (a b : Fin N) (hi : Set.InjOn A.label (A.pathUnion a b)) :
    (A.pathRootEdges a b).image (Finset.image (A.pathAssignment a b hi)) =
      (A.seed.backEdges A.roots).image (Finset.image A.label) := by
  classical
  unfold pathRootEdges
  rw [Finset.image_image]
  apply Finset.image_congr
  intro e he
  have hs : e ⊆ A.pathUnion a b := by
    obtain ⟨v,hv,u,hu,rfl⟩ := A.seed.backEdges_mem_pair he
    have hvR : v.val < R := (Finset.mem_filter.mp hv).2
    have hul : u.val < v.val := A.seed.older_lt v u hu
    have huR : u.val < R := hul.trans hvR
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x
      exact (A.mem_pathUnion a b u).mpr (Or.inl huR)
    · have hx' := Finset.mem_singleton.mp hx
      subst x
      exact (A.mem_pathUnion a b v).mpr (Or.inl hvR)
  change (reindexSet (A.pathUnion a b) e).image
    (fun i => A.label ((A.pathUnion a b).orderEmbOfFin rfl i)) = e.image A.label
  change (reindexSet (A.pathUnion a b) e).image
    (A.label ∘ (A.pathUnion a b).orderEmbOfFin rfl) = e.image A.label
  rw [← Finset.image_image,image_reindexSet hs]

end TriangleGrowth
namespace RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

lemma growth_seed_image (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G) :
    ((F.toTriangleGrowth hM hG).seed.backEdges (F.toTriangleGrowth hM hG).roots).image
      (Finset.image (F.toTriangleGrowth hM hG).label) = c.focus :=
  matchingSeed_full_image F.vertexLabel c.focus hM F.vertexLabel_injective_roots F.vertexLabel_covers

end RecordedCallForest

noncomputable def embeddedWitnessRoots {n R d : ℕ} {G : Graph n}
    (W : BoundedEmbeddedWitness G R d) : Graph n :=
  W.2.1.val.image (fun e => e.image W.2.2.2.val)

end SharpTerminalLeave

end

end OAI
