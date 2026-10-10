import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.LookupGraph
import OAI.Combinatorics.TriangleRemoval.Process.NonrootForest
import OAI.Combinatorics.TriangleRemoval.Process.PathPattern
import OAI.Combinatorics.TriangleRemoval.Process.ValidIndexedAttachments
import OAI.Combinatorics.TriangleRemoval.Coupling.OrderedSuffix

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

lemma reindexSet_pair {N : ℕ} (S : Finset (Fin N)) (x y : Fin N)
    (hx : x ∈ S) (hy : y ∈ S) :
    reindexSet S {x,y} = {PathForest.index S x hx,PathForest.index S y hy} := by
  ext i
  simp only [mem_reindexSet,Finset.mem_insert,Finset.mem_singleton]
  have hxi : S.orderEmbOfFin rfl i = x ↔ i = PathForest.index S x hx := by
    simpa only [PathForest.embed_index] using
      ((S.orderEmbOfFin rfl).injective.eq_iff (a := i) (b := PathForest.index S x hx))
  have hyi : S.orderEmbOfFin rfl i = y ↔ i = PathForest.index S y hy := by
    simpa only [PathForest.embed_index] using
      ((S.orderEmbOfFin rfl).injective.eq_iff (a := i) (b := PathForest.index S y hy))
  rw [hxi,hyi]

lemma PathForest.restrict_parent_none {s : ℕ} (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S) (i : Fin S.card) :
    (F.restrict S hS).parent i = none ↔ F.parent (S.orderEmbOfFin rfl i) = none := by
  classical
  change F.restrictedParent S hS i = none ↔ _
  unfold PathForest.restrictedParent
  split <;> simp_all

namespace TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

lemma suffix_eq_ordered (a b : Fin N) : A.pathSuffix a b R = orderedSuffix (A.pathUnion a b) R := rfl

noncomputable def pathBirthIndex (a b : Fin N) (hR : R ≤ N)
    (i : Fin (A.pathSuffix a b R).card) : Fin (A.pathUnion a b).card :=
  suffixFullIndex (A.pathUnion a b) hR
    (fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx)) i

@[simp] lemma pathBirthIndex_val (a b : Fin N) (hR : R ≤ N)
    (i : Fin (A.pathSuffix a b R).card) : (A.pathBirthIndex a b hR i).val = R+i.val := rfl

@[simp] lemma pathBirthIndex_embedding (a b : Fin N) (hR : R ≤ N)
    (i : Fin (A.pathSuffix a b R).card) :
    (A.pathUnion a b).orderEmbOfFin rfl (A.pathBirthIndex a b hR i) =
      (A.pathSuffix a b R).orderEmbOfFin rfl i :=
  suffix_full_embedding _ hR _ i

noncomputable def pathAttachments (a b : Fin N) (hR : R ≤ N)
    (i : Fin (A.pathSuffix a b R).card) : Finset (Fin (A.pathUnion a b).card) :=
  (A.pathPattern a b).older (A.pathBirthIndex a b hR i)

lemma pathAttachments_eq (a b : Fin N) (hR : R ≤ N)
    (i : Fin (A.pathSuffix a b R).card) :
    A.pathAttachments a b hR i = reindexSet (A.pathUnion a b)
      (A.older ((A.pathSuffix a b R).orderEmbOfFin rfl i)) := by
  change reindexSet _ (A.older ((A.pathUnion a b).orderEmbOfFin rfl _)) = _
  rw [A.pathBirthIndex_embedding]

noncomputable def pathRootEdges (a b : Fin N) : Finset (Finset (Fin (A.pathUnion a b).card)) :=
  (A.seed.backEdges A.roots).image (reindexSet (A.pathUnion a b))

lemma pathForest_parent_some (a b : Fin N) (i j : Fin (A.pathSuffix a b R).card) :
    (A.pathForest a b).parent i = some j ↔
      A.parent ((A.pathSuffix a b R).orderEmbOfFin rfl i) =
        some ((A.pathSuffix a b R).orderEmbOfFin rfl j) := by
  rw [pathForest,PathForest.restrict_parent_some]
  change (if R ≤ _ then _ else none) = _ ↔ _
  rw [ite_eq_left ((A.mem_pathSuffix a b _ R).mp
    ((A.pathSuffix a b R).orderEmbOfFin_mem rfl i)).2]

lemma pathForest_parent_none (a b : Fin N) (i : Fin (A.pathSuffix a b R).card) :
    (A.pathForest a b).parent i = none ↔
      A.parent ((A.pathSuffix a b R).orderEmbOfFin rfl i) = none := by
  rw [pathForest,PathForest.restrict_parent_none]
  change (if R ≤ _ then _ else none) = _ ↔ _
  rw [ite_eq_left ((A.mem_pathSuffix a b _ R).mp
    ((A.pathSuffix a b R).orderEmbOfFin_mem rfl i)).2]

theorem pathAttachments_valid (a b : Fin N) (hR : R ≤ N) :
    ValidIndexedAttachments (A.pathRootEdges a b) (A.pathBirthIndex a b hR)
      (A.pathForest a b) (A.pathAttachments a b hR) := by
  classical
  constructor
  · intro i
    exact le_of_eq (A.pathPattern_nonroot a b _ (by simp only [pathBirthIndex_val]; omega))
  · intro i
    have hiv := (A.pathSuffix a b R).orderEmbOfFin_mem rfl i
    have hiR := ((A.mem_pathSuffix a b _ R).mp hiv).2
    cases hp : (A.pathForest a b).parent i with
    | none =>
      have hpar := (A.pathForest_parent_none a b i).mp hp
      obtain ⟨x,y,hx,hy,hxy,he⟩ := A.older_pair_of_root hiR hpar
      have hem : ({x,y} : Finset (Fin N)) ∈ A.seed.backEdges A.roots := by
        rcases hxy with hxy | hyx
        · exact Finset.mem_biUnion.mpr ⟨y,(A.mem_roots y).mpr hy,
            Finset.mem_image.mpr ⟨x,hxy,rfl⟩⟩
        · have hh : ({y,x} : Finset (Fin N)) ∈ A.seed.backEdges A.roots :=
            Finset.mem_biUnion.mpr ⟨x,(A.mem_roots x).mpr hx,
              Finset.mem_image.mpr ⟨y,hyx,rfl⟩⟩
          simpa only [Finset.pair_comm] using hh
      change A.pathAttachments a b hR i ∈ A.pathRootEdges a b
      rw [A.pathAttachments_eq,he]
      exact Finset.mem_image.mpr ⟨{x,y},hem,rfl⟩
    | some j =>
      have hpar := (A.pathForest_parent_some a b i j).mp hp
      obtain ⟨u,hu,he⟩ := A.older_focus hiR hpar
      have hjP := ((A.mem_pathSuffix a b _ R).mp
        ((A.pathSuffix a b R).orderEmbOfFin_mem rfl j)).1
      have huP := A.pathUnion_older_closed hjP hu
      let k := PathForest.index (A.pathUnion a b) u huP
      refine ⟨k,?_,?_⟩
      · rw [A.pathAttachments_eq]
        apply (mem_reindexSet _ _ _).mpr
        simpa only [k,PathForest.embed_index] using hu
      · rw [A.pathAttachments_eq,he,reindexSet_pair _ _ _ hjP huP]
        have hj : PathForest.index (A.pathUnion a b)
            ((A.pathSuffix a b R).orderEmbOfFin rfl j) hjP = A.pathBirthIndex a b hR j := by
          apply (A.pathUnion a b).orderEmbOfFin rfl |>.injective
          rw [PathForest.embed_index,A.pathBirthIndex_embedding]
        rw [hj]

end TriangleGrowth
end SharpTerminalLeave

open scoped BigOperators

end

end OAI
