import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedLoss
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedEndpoint

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

def keptCount (R : A→B→Prop) (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (i : I) (U : Domains A B) (x : α i) : ℝ :=
  match choose i x U with
  | none=>0
  | some c=>compatible R (read i x U c) (targets i)

omit [DecidableEq I] in
lemma fullOutput_length_accrued (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B) :
    ((fullOutput R choose read targets z t U).length:ℝ)=
      accrued choose read (keptCount R choose read targets) z t U := by
  induction t generalizing U with
  | nil=>simp only [fullOutput_nil,List.length_nil,Nat.cast_zero,accrued]
  | node i l r hl hr=>
    cases hc : choose i (z i) U with
    | none=>simp only [fullOutput_fail R choose read targets z i l r U hc,
        accrued,keptCount,hc,add_zero,List.length_nil,Nat.cast_zero]
    | some c=>
      rw [fullOutput_success R choose read targets z i l r U c hc]
      simp only [List.length_append,Nat.cast_add,hl,hr,accrued,keptCount,hc]
      dsimp only [compatible]
      ring

lemma population_length_sum (targets : I→List (A×B)) (t : BinaryTree I)
    (ht : Separated t) :
    ((population targets t).length:ℝ)=∑ i∈labels t,((targets i).length:ℝ) := by
  induction t with
  | nil=>simp only [population,labels_nil,List.length_nil,Nat.cast_zero,sum_empty]
  | node i l r hl hr=>
    rcases ht with ⟨htl,htr,hli,hri,hd⟩
    rw [labels_node,sum_insert (by simp only [mem_union,not_or]; exact ⟨hli,hri⟩),sum_union hd]
    simp only [population,List.length_append,Nat.cast_add,hl htl,hr htr]
    ring

omit [DecidableEq I] in
lemma compatible_complement (R : A→B→Prop) (V : Domains A B) (xs : List (A×B))
    (hR : ∀ x∈xs,R x.1 x.2) :
    (xs.map (fun x=>if x.1∈V.1 ∧ x.2∈V.2 then (0:ℝ) else 1)).sum=
      (xs.length:ℝ)-compatible R V xs := by
  induction xs with
  | nil=>simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.cast_zero,
      compatible,List.filter_nil,sub_self]
  | cons x xs ih=>
    have hx : R x.1 x.2 := hR x (List.mem_cons_self ..)
    have ht : ∀ y∈xs,R y.1 y.2 := fun y hy=>hR y (List.mem_cons_of_mem _ hy)
    have hm : x∈flagDomain R V ↔ x.1∈V.1 ∧ x.2∈V.2 := by
      simp only [flagDomain,mem_filter,mem_product,hx,and_true]
    by_cases hc : x.1∈V.1 ∧ x.2∈V.2
    · have hxV : x∈flagDomain R V := hm.mpr hc
      simp only [List.map_cons,List.sum_cons,ite_eq_left hc,zero_add,ih ht,
        List.length_cons,Nat.cast_add,Nat.cast_one,compatible,List.filter_cons_of_pos (p:=fun z=>decide (z∈flagDomain R V)) (a:=x) (l:=xs) (by simpa only [decide_eq_true_eq] using hxV),
        List.length_cons,Nat.cast_add,Nat.cast_one]
      ring
    · have hxV : x∉flagDomain R V := fun h=>hc (hm.mp h)
      simp only [List.map_cons,List.sum_cons,ite_eq_right hc,ih ht,
        List.length_cons,Nat.cast_add,Nat.cast_one,compatible,List.filter_cons_of_neg (p:=fun z=>decide (z∈flagDomain R V)) (a:=x) (l:=xs) (by simpa only [decide_eq_true_eq] using hxV)]
      ring

lemma pivot_count_complement (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (i : I) (t : BinaryTree I) (U : Domains A B)
    (hR : ∀ x∈targets i,R x.1 x.2) :
    ((targets i).map (fun x=>targetFailure choose read x.1 x.2 i t U z)).sum=
      ((targets i).length:ℝ)-produced choose read i (keptCount R choose read targets i) t U z := by
  have hones (xs : List (A×B)) : (xs.map (fun _=>(1:ℝ))).sum=(xs.length:ℝ) := by
    induction xs with
    | nil=>simp
    | cons x xs ih=>simp only [List.map_cons,List.sum_cons,ih,List.length_cons,
        Nat.cast_add,Nat.cast_one]; ring
  cases ha : arrive choose read z i t U with
  | none=>simpa only [targetFailure,ha,produced,sub_zero] using hones (targets i)
  | some V=>
    cases hc : choose i (z i) V with
    | none=>simpa only [targetFailure,ha,hc,produced,keptCount,sub_zero] using hones (targets i)
    | some c=>
      simp only [targetFailure,ha,hc,produced,keptCount]
      exact compatible_complement R (read i (z i) V c) (targets i) hR

theorem output_loss_eq_targets (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hR : ∀ i∈labels t,∀ x∈targets i,R x.1 x.2) :
    ((population targets t).length:ℝ)-(fullOutput R choose read targets z t U).length=
      ∑ i∈labels t,((targets i).map (fun x=>targetFailure choose read x.1 x.2 i t U z)).sum := by
  rw [population_length_sum targets t ht,fullOutput_length_accrued,
    accrued_eq_sum choose read _ z t U ht,←sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  exact (pivot_count_complement R choose read targets z i t U (hR i hi)).symm

end
end SharpLogRamsey.FreshExecution

end

end OAI
