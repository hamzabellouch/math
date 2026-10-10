import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.LookupGraph
import OAI.Combinatorics.TriangleRemoval.Process.RestrictedParent
import OAI.Combinatorics.TriangleRemoval.Coupling.OrderedSuffix
import OAI.Combinatorics.TriangleRemoval.Queries.MarkedIndexedAttachmentPattern
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

def suffixProjection {K R s : ℕ} (hK : K = R+s) (i : Fin K) : Option (Fin s) :=
  if h : R ≤ i.val then some ⟨i.val-R,by omega⟩ else none

lemma suffix_projection_embedding {N R : ℕ} (S : Finset (Fin N)) (hR : R ≤ N)
    (hroot : ∀ x : Fin N, x.val < R → x ∈ S) (x : Fin N) (hx : x ∈ S) :
    suffixProjection (prefix_suffix_card S hR hroot) (PathForest.index S x hx) =
      PathForest.restrictMark (orderedSuffix S R) x := by
  classical
  by_cases hn : R ≤ x.val
  · have hxT : x ∈ orderedSuffix S R := Finset.mem_filter.mpr ⟨hx,hn⟩
    let i := PathForest.index (orderedSuffix S R) x hxT
    have hs : PathForest.index S x hx = suffixFullIndex S hR hroot i := by
      apply (S.orderEmbOfFin rfl).injective
      rw [PathForest.embed_index,suffix_full_embedding]
      exact (PathForest.embed_index _ _ _).symm
    have hiv : (PathForest.index S x hx).val = R+i.val := by rw [hs]; rfl
    rw [PathForest.restrictMark,dite_eq_left hxT]
    unfold suffixProjection
    rw [dite_eq_left (show R ≤ (PathForest.index S x hx).val by omega)]
    apply congrArg some
    apply Fin.ext
    simp only [hiv]
    exact Nat.add_sub_cancel_left R i.val
  · have hxT : x ∉ orderedSuffix S R := by simpa only [orderedSuffix,Finset.mem_filter,hx,true_and] using hn
    have hiv : (PathForest.index S x hx).val = x.val := initial_rank S hroot x (by omega)
    rw [PathForest.restrictMark,dite_eq_right hxT]
    unfold suffixProjection
    rw [dite_eq_right (show ¬ R ≤ (PathForest.index S x hx).val by omega)]

namespace TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

lemma path_card_split (a b : Fin N) (hR : R ≤ N) :
    (A.pathUnion a b).card = R+(A.pathSuffix a b R).card :=
  prefix_suffix_card _ hR (fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx))

lemma path_mark_projection (a b : Fin N) (hR : R ≤ N)
    (x : Fin N) (hx : x ∈ A.pathUnion a b) :
    suffixProjection (A.path_card_split a b hR) (A.pathIndex a b x hx) =
      PathForest.restrictMark (A.pathSuffix a b R) x :=
  suffix_projection_embedding _ hR
    (fun y hy => (A.mem_pathUnion a b y).mpr (Or.inl hy)) x hx

open Classical in

noncomputable def pathWitnessCode (a b : Fin N) (hR : R ≤ N) :
    Σ ab : Fin (A.pathUnion a b).card × Fin (A.pathUnion a b).card,
      Σ F : {F : PathForest (A.pathSuffix a b R).card // ∀ i,
        F.OnPath (suffixProjection (A.path_card_split a b hR) ab.1) i ∨
        F.OnPath (suffixProjection (A.path_card_split a b hR) ab.2) i},
        {f // f ∈ indexedAttachmentFamily (A.pathRootEdges a b) (A.pathBirthIndex a b hR) F.val} := by
  refine ⟨⟨A.pathIndex a b a (A.left_mem_pathUnion a b),
    A.pathIndex a b b (A.right_mem_pathUnion a b)⟩,⟨A.pathForest a b,?_⟩,
    A.pathAttachments a b hR,?_⟩
  · rw [A.path_mark_projection a b hR a (A.left_mem_pathUnion a b),
      A.path_mark_projection a b hR b (A.right_mem_pathUnion a b)]
    exact A.pathForest_two_path_cover a b
  · exact (mem_indexedAttachmentFamily _ _ _ _).mpr (A.pathAttachments_valid a b hR)

lemma pathRootEdges_count (a b : Fin N) :
    (A.pathRootEdges a b).card ≤ (A.seed.backEdges A.roots).card := Finset.card_image_le

open Classical in

theorem path_witness_code_count (a b : Fin N) (hR : R ≤ N)
    (hE : (A.seed.backEdges A.roots).card ≤ 2) :
    Fintype.card (Σ ab : Fin (A.pathUnion a b).card × Fin (A.pathUnion a b).card,
      Σ F : {F : PathForest (A.pathSuffix a b R).card // ∀ i,
        F.OnPath (suffixProjection (A.path_card_split a b hR) ab.1) i ∨
        F.OnPath (suffixProjection (A.path_card_split a b hR) ab.2) i},
        {f // f ∈ indexedAttachmentFamily (A.pathRootEdges a b) (A.pathBirthIndex a b hR) F.val}) ≤
      (R+(A.pathSuffix a b R).card)^2 * 6^(A.pathSuffix a b R).card := by
  simpa only [Fintype.card_fin,A.path_card_split a b hR] using
    all_marked_indexed_attachment_pattern_count (A.pathRootEdges a b) (A.pathBirthIndex a b hR)
      ((A.pathRootEdges_count a b).trans hE) (suffixProjection (A.path_card_split a b hR))

end TriangleGrowth
end SharpTerminalLeave

end

end OAI
