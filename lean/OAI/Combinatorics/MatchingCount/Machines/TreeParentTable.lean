import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPProgram
import OAI.Combinatorics.MatchingCount.Machines.TreeIndex
import OAI.Combinatorics.MatchingCount.Machines.TreeLabelCorrect

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck

def parentKey (x : HierarchyInput×LabelKey) : LabelKey :=
  (x.2.1-1,labelRoot (x.1,(x.2.1-1,x.2.2)))
def parentKeyRealizer : Realizer parentKey := by
  let p : Realizer (fun x : HierarchyInput×LabelKey=>(x.2.1-1,x.2.2)) := pair (composition second.fst predecessor) second.snd
  exact (pair (composition second.fst predecessor) (composition (pair first p) labelRootRealizer)).congr (fun _=>rfl)
lemma polynomial_parentKey : PolynomialTime parentKeyRealizer := by
  unfold parentKeyRealizer Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  have := polynomial_predecessor
  have := polynomial_labelRoot
  tree_cost

def parentEntry (x : (HierarchyInput×List LabelKey)×LabelKey) : Bool×ℕ :=
  if x.2.1=0 then (false,0) else (true,x.1.2.idxOf (parentKey (x.1.1,x.2)))
def parentEntryRealizer : Realizer parentEntry :=
  (choose (composition (pair second.fst (constant 0)) natEqual) (constant (false,0))
    (pair (constant true) (composition (pair (composition (pair first.fst second) parentKeyRealizer) first.snd)
      (indexOf (pairEqual natEqual natEqual))))).congr (fun x=>by simp only [parentEntry,Function.comp_apply,decide_eq_true_eq])
lemma polynomial_parentEntry : PolynomialTime parentEntryRealizer := by
  unfold parentEntryRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_parentKey
  have := polynomial_indexOf (polynomial_pairEqual polynomial_natEqual polynomial_natEqual)
  tree_cost

def parents (x : HierarchyInput) : ExecutableDP.Parents :=
  (labels x).map fun l=>parentEntry ((x,labels x),l)
def parentsRealizer : Realizer parents := composition (pair (pair identity labelsRealizer) labelsRealizer) (mapWith parentEntryRealizer)
lemma polynomial_parents : PolynomialTime parentsRealizer := by
  unfold parentsRealizer
  exact polynomial_composition (polynomial_pair (polynomial_pair polynomial_identity polynomial_labels) polynomial_labels)
    (polynomial_mapWith polynomial_parentEntry)

def ranks (x : HierarchyInput) : List ℕ := (labels x).map Prod.fst
def ranksRealizer : Realizer ranks := composition labelsRealizer (map first)
lemma polynomial_ranks : PolynomialTime ranksRealizer := polynomial_composition polynomial_labels (polynomial_map polynomial_first)

lemma idxOf_map_inj {A C : Type} [BEq A] [LawfulBEq A] [BEq C] [LawfulBEq C] (f : A→C)
    (hf : Function.Injective f) (a : A) (xs : List A) : (xs.map f).idxOf (f a)=xs.idxOf a := by
  induction xs with
  | nil=>simp
  | cons b bs ih=>
    simp only [List.map_cons,List.idxOf_cons]
    have he : (f b==f a)=(b==a) := by apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq, hf.eq_iff]
    rw [he,ih]

local instance {n H : ℕ} (B : Fin n→Fin n→ℚ) : LinearOrder (NumberedHierarchy.Label B H) := NumberedHierarchy.labelOrder B H
local instance (priority := 2000) {n H : ℕ} (B : Fin n→Fin n→ℚ) : LE (NumberedHierarchy.Label B H) := (NumberedHierarchy.labelOrder B H).toLE
lemma index_key {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (xs : List Bool) (a : NumberedHierarchy.Label B xs.length) :
    (labels (matrixRep B,xs)).idxOf (key a)=((UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)).symm a).val := by
  rw [labels_eq_ofFn B hB]
  let e := UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)
  let i := e.symm a
  have hn := List.nodup_ofFn.mpr ((key_injective B).comp e.injective)
  have hi : i.val < (List.ofFn (fun j=>key (e j))).length := by simpa only [List.length_ofFn] using i.isLt
  have he := @List.Nodup.idxOf_getElem LabelKey (inferInstance : BEq LabelKey) inferInstance _ hn i.val hi
  simp only [List.getElem_ofFn,Fin.eta,i,Function.comp_apply,Equiv.apply_symm_apply] at he
  convert he using 1
  rfl

lemma parentKey_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) (a : NumberedHierarchy.Label B xs.length) (ha : 0<a.1.val) :
    parentKey ((matrixRep B,xs),key a)=key (NumberedHierarchy.labelAt B hsym htri (H:=xs.length) ⟨a.1.val-1,by omega⟩ a.2.val) := by
  apply Prod.ext
  · rfl
  exact labelRoot_matrixRep B hB xs ⟨a.1.val-1,by omega⟩ a.2.val

lemma parentEntry_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) (a : NumberedHierarchy.Label B xs.length) :
    parentEntry (((matrixRep B,xs),labels (matrixRep B,xs)),key a)=
      ExecutableDP.parentTag ((NumberedHierarchy.parent B hsym htri a).map
        (UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)).symm) := by
  by_cases ha : 0<a.1.val
  · simp only [parentEntry,key,show ¬a.1.val=0 by omega,↓reduceIte,NumberedHierarchy.parent,ha,↓reduceDIte,Option.map_some,ExecutableDP.parentTag]
    rw [parentKey_eq B hB hsym htri xs a ha,index_key B hB]
  · have hz : a.1.val=0 := by omega
    simp [parentEntry,hz,NumberedHierarchy.parent,ExecutableDP.parentTag]

lemma parents_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) :
    parents (matrixRep B,xs)=ExecutableDP.parentRep (UnitRefresh.numberedParent (NumberedHierarchy.parent B hsym htri (H:=xs.length))) := by
  unfold parents
  rw [labels_eq_ofFn B hB,List.map_ofFn]
  unfold ExecutableDP.parentRep
  congr 1
  funext i
  simpa only [Function.comp_apply,←labels_eq_ofFn B hB,UnitRefresh.numberedParent] using parentEntry_eq B hB hsym htri xs (UnitRefresh.orderedEnum _ i)
lemma ranks_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b) (xs : List Bool) :
    ranks (matrixRep B,xs)=List.ofFn (UnitRefresh.numberedRank (fun a : NumberedHierarchy.Label B xs.length=>a.1.val)) := by
  unfold ranks
  rw [labels_eq_ofFn B hB,List.map_ofFn]
  rfl
end MatchingFPRAS.ExecutableHierarchy

end OAI
