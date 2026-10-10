import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedSecondTrim

namespace OAI

section
namespace SharpLogRamsey.ChronologicalTree
open BinaryTree Finset FreshExecution
open scoped Classical
noncomputable section

lemma balanced_inorder (lo n : ℕ) : inorder (balanced lo n)=List.range' lo n := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    rw [balanced]
    split_ifs with hn
    · simp [hn,inorder]
    · simp only [inorder]
      rw [ih (n/2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)),
        ih (n-n/2-1) (by omega)]
      rw [←List.range'_succ, List.range'_append_1]
      congr 1
      have : n/2<n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      omega

lemma inorder_map {A B : Type*} (f : A→B) (t : BinaryTree A) :
    inorder (t.map f)=(inorder t).map f := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp [BinaryTree.map,inorder,hl,hr]

lemma map_range_getD {A : Type*} (l : List A) (a : A) :
    (List.range l.length).map (fun i=>l.getD i a)=l := by
  apply List.ext_getElem
  · simp
  · intro i hi ho
    simp only [List.getElem_map,List.getElem_range]
    exact List.getD_eq_getElem l a ho

variable {I : Type*} [LinearOrder I]
local instance liveEq : DecidableEq I := Classical.decEq _

def liveTree (S : Finset I) (fallback : I) : BinaryTree I :=
  (balanced 0 S.card).map (fun j=>(S.sort (·≤·)).getD j fallback)

lemma liveTree_inorder (S : Finset I) (fallback : I) :
    inorder (liveTree S fallback)=S.sort (·≤·) := by
  rw [liveTree,inorder_map,balanced_inorder,←List.range_eq_range']
  simpa only [length_sort] using map_range_getD (S.sort (·≤·)) fallback

lemma liveTree_labels (S : Finset I) (fallback : I) : labels (liveTree S fallback)=S := by
  rw [labels,liveTree_inorder]
  exact sort_toFinset _ _

lemma liveTree_nodes (S : Finset I) (fallback : I) : (liveTree S fallback).numNodes=S.card := by
  rw [←inorder_length,liveTree_inorder,length_sort]

lemma map_height {A B : Type*} (f : A→B) (t : BinaryTree A) : (t.map f).height=t.height := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp [BinaryTree.map,height,hl,hr]

lemma liveTree_height (S : Finset I) (fallback : I) :
    (liveTree S fallback).height≤Nat.log 2 S.card+1 := by
  rw [liveTree,map_height]
  exact balanced_height _ _

lemma liveTree_nodup (S : Finset I) (fallback : I) :
    (inorder (liveTree S fallback)).Nodup := by
  rw [liveTree_inorder]
  exact sort_nodup _ _

lemma liveTree_separated (S : Finset I) (fallback : I) : Separated (liveTree S fallback) :=
  separated_of_nodup _ (liveTree_nodup S fallback)

lemma ordered_leftPath (t : BinaryTree I) (ht : (inorder t).Pairwise (·<·))
    (target i : I) (hi : i∈leftPath target t) : target < i := by
  induction t with
  | nil => simp [leftPath] at hi
  | node a l r hl hr =>
    simp only [inorder,List.pairwise_append,List.pairwise_cons] at ht
    rw [leftPath] at hi
    split_ifs at hi with ha hL
    · simp at hi
    · rcases mem_insert.mp hi with rfl|hi
      · exact ht.2.2 target (by simpa only [labels,List.mem_toFinset] using hL) i (List.mem_cons_self ..)
      · exact hl ht.1 hi
    · exact hr ht.2.1.2 hi

lemma ordered_rightPath (t : BinaryTree I) (ht : (inorder t).Pairwise (·<·))
    (target i : I) (hi : i∈rightPath target t) : i < target := by
  induction t with
  | nil => simp [rightPath] at hi
  | node a l r hl hr =>
    simp only [inorder,List.pairwise_append,List.pairwise_cons] at ht
    rw [rightPath] at hi
    split_ifs at hi with ha hR
    · simp at hi
    · rcases mem_insert.mp hi with rfl|hi
      · exact ht.2.1.1 target (by simpa only [labels,List.mem_toFinset] using hR)
      · exact hr ht.2.1.2 hi
    · exact hl ht.1 hi

lemma liveTree_ordered (S : Finset I) (fallback : I) :
    (inorder (liveTree S fallback)).Pairwise (·<·) := by
  rw [liveTree_inorder]
  exact S.sortedLT_sort.pairwise

lemma liveTree_left (S : Finset I) (fallback target i : I)
    (hi : i∈leftPath target (liveTree S fallback)) : target < i :=
  ordered_leftPath _ (liveTree_ordered S fallback) target i hi

lemma liveTree_right (S : Finset I) (fallback target i : I)
    (hi : i∈rightPath target (liveTree S fallback)) : i < target :=
  ordered_rightPath _ (liveTree_ordered S fallback) target i hi

end
end SharpLogRamsey.ChronologicalTree

end

end OAI
