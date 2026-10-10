import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.BornEdges
import OAI.Combinatorics.TriangleRemoval.Queries.RecordedCallForest
import OAI.Combinatorics.TriangleRemoval.Process.EdgeMatching
import OAI.Combinatorics.TriangleRemoval.Embeddings.PathBirthIndex

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

def indexedPatternEdges {K s : ℕ} (E : Finset (Finset (Fin K)))
    (birth : Fin s → Fin K) (f : Fin s → Finset (Fin K)) : Finset (Finset (Fin K)) :=
  E ∪ Finset.univ.biUnion (fun i => (f i).image (fun u => {u,birth i}))

namespace TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

theorem pathPattern_edges (a b : Fin N) (hR : R ≤ N) :
    (A.pathPattern a b).backEdges Finset.univ =
      indexedPatternEdges (A.pathRootEdges a b) (A.pathBirthIndex a b hR)
        (A.pathAttachments a b hR) := by
  classical
  let S := A.pathUnion a b
  have hroot : ∀ x : Fin N, x.val < R → x ∈ S :=
    fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx)
  ext e
  constructor
  · intro he
    obtain ⟨v,_,u,hu,rfl⟩ := (A.pathPattern a b).backEdges_mem_pair he
    by_cases hv : v.val < R
    · have hvR : (S.orderEmbOfFin rfl v).val < R := by
        rw [orderEmb_initial S hR hroot v hv]
        exact hv
      have hu' : S.orderEmbOfFin rfl u ∈ A.seed.older (S.orderEmbOfFin rfl v) := by
        change u ∈ reindexSet S (A.older (S.orderEmbOfFin rfl v)) at hu
        rw [mem_reindexSet] at hu
        rwa [A.older_eq_seed hvR] at hu
      have hem : ({S.orderEmbOfFin rfl u,S.orderEmbOfFin rfl v} : Finset (Fin N)) ∈
          A.seed.backEdges A.roots :=
        Finset.mem_biUnion.mpr ⟨_,(A.mem_roots _).mpr hvR,Finset.mem_image.mpr ⟨_,hu',rfl⟩⟩
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨_,hem,?_⟩
      rw [reindexSet_pair S _ _ (S.orderEmbOfFin_mem rfl u) (S.orderEmbOfFin_mem rfl v)]
      simp only [PathForest.index_embed]
    · have hs : (A.pathUnion a b).card = R + (A.pathSuffix a b R).card :=
        prefix_suffix_card S hR hroot
      let j : Fin (A.pathSuffix a b R).card := ⟨v.val-R,by omega⟩
      have hj : A.pathBirthIndex a b hR j = v := by
        apply Fin.ext
        simp only [pathBirthIndex_val,j]
        omega
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨u,?_,?_⟩⟩
      · change u ∈ (A.pathPattern a b).older (A.pathBirthIndex a b hR j)
        rwa [hj]
      · rw [hj]
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨v,hv,u,hu,rfl⟩ := A.seed.backEdges_mem_pair hf
      have hvR := (A.mem_roots v).mp hv
      have huR := A.seed_root v u hu hvR
      have hvP := hroot v hvR
      have huP := hroot u huR
      rw [reindexSet_pair S u v huP hvP]
      apply Finset.mem_biUnion.mpr
      refine ⟨PathForest.index S v hvP,Finset.mem_univ _,Finset.mem_image.mpr
        ⟨PathForest.index S u huP,?_,rfl⟩⟩
      change PathForest.index S u huP ∈
        reindexSet S (A.older (S.orderEmbOfFin rfl (PathForest.index S v hvP)))
      rw [mem_reindexSet]
      rw [PathForest.embed_index,PathForest.embed_index,A.older_eq_seed hvR]
      exact hu
    · obtain ⟨i,_,he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_biUnion.mpr ⟨A.pathBirthIndex a b hR i,Finset.mem_univ _,
        Finset.mem_image.mpr ⟨u,hu,rfl⟩⟩

theorem pathAssignment_mem_decoded {a b : Fin N} (hR : R ≤ N)
    (hi : Set.InjOn A.label (A.pathUnion a b))
    (he : A.birthGraph.ExtraEdge (lookupGraph G) A.label a b) :
    A.pathAssignment a b hi ∈ graphEmbeddingSet
      (insert ({A.pathIndex a b a (A.left_mem_pathUnion a b),
        A.pathIndex a b b (A.right_mem_pathUnion a b)} : Finset _)
        (indexedPatternEdges (A.pathRootEdges a b) (A.pathBirthIndex a b hR)
          (A.pathAttachments a b hR))) G := by
  rw [← A.pathPattern_edges a b hR]
  exact A.pathAssignment_mem hi he

end TriangleGrowth
end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
