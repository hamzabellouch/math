import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.FreshAccrual

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

def compatible (R : A→B→Prop) (U : Domains A B) (xs : List (A×B)) : ℝ :=
  (xs.filter (fun z=>z∈flagDomain R U)).length

lemma compatible_append (R : A→B→Prop) (U : Domains A B) (xs ys : List (A×B)) :
    compatible R U (xs++ys)=compatible R U xs+compatible R U ys := by
  simp only [compatible,List.filter_append,List.length_append,Nat.cast_add]

lemma retained_all (R : A→B→Prop) (U : Domains A B) (xs : List (A×B)) :
    retained R U xs xs.length=xs.filter (fun z=>z∈flagDomain R U) := by
  exact List.take_of_length_le (List.length_filter_le _ _)

def fullOutput (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B) : List (A×B) :=
  output R (fixedRead read z) targets (fun i=>(targets i).length)
    (execute (fixedRead read z) (fixedChoose choose z) t U) U

omit [DecidableEq I] in
lemma fullOutput_nil (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (U : Domains A B) :
    fullOutput R choose read targets z .nil U=[] := rfl

omit [DecidableEq I] in
lemma fullOutput_fail (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (i : I) (l r : BinaryTree I) (U : Domains A B)
    (hc : choose i (z i) U=none) :
    fullOutput R choose read targets z (.node i l r) U=[] := by
  simp only [fullOutput,execute,fixedChoose,hc,Option.map_none,output]

omit [DecidableEq I] in
lemma fullOutput_success (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (i : I) (l r : BinaryTree I) (U : Domains A B)
    (c : C) (hc : choose i (z i) U=some c) :
    let V:=read i (z i) U c
    fullOutput R choose read targets z (.node i l r) U=
      fullOutput R choose read targets z l (V.1,U.2)++
      (targets i).filter (fun x=>x∈flagDomain R V)++
      fullOutput R choose read targets z r (U.1,V.2) := by
  simp only [fullOutput,execute,fixedChoose,hc,Option.map_some,output,fixedRead,retained_all]

def nodeCharge (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (i : I) (l r : BinaryTree I) (U : Domains A B) (x : α i) : ℝ :=
  compatible R U (population targets (.node i l r))-
    match choose i x U with
    | none=>0
    | some c=>
      let V:=read i x U c
      compatible R (V.1,U.2) (population targets l)+
        compatible R V (targets i)+compatible R (U.1,V.2) (population targets r)

def charges (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B)) :
    BinaryTree I→∀ i,Domains A B→α i→ℝ
  | .nil,_,_,_=>0
  | .node j l r,i,U,x=>if i=j then nodeCharge R choose read targets i l r U x
      else if i∈labels l then charges R choose read targets l i U x
      else charges R choose read targets r i U x

lemma accrued_congr (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (f g : ∀ i,Domains A B→α i→ℝ)
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B)
    (h : ∀ i∈labels t,∀ V x,f i V x=g i V x) :
    accrued choose read f z t U=accrued choose read g z t U := by
  induction t generalizing U with
  | nil=>rfl
  | node i l r hl hr=>
    have hi : i∈labels (.node i l r) := by rw [labels_node]; exact mem_insert_self _ _
    have hL : ∀ j∈labels l,∀ V x,f j V x=g j V x := by
      intro j hj
      exact h j (by rw [labels_node]; exact mem_insert_of_mem (mem_union_left _ hj))
    have hR : ∀ j∈labels r,∀ V x,f j V x=g j V x := by
      intro j hj
      exact h j (by rw [labels_node]; exact mem_insert_of_mem (mem_union_right _ hj))
    rw [accrued,accrued,h i hi]
    cases choose i (z i) U with
    | none=>rfl
    | some c=>dsimp only; rw [hl _ hL,hr _ hR]

theorem output_loss_eq_accrued (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B) (ht : Separated t) :
    compatible R U (population targets t)-
      (fullOutput R choose read targets z t U).length=
      accrued choose read (charges R choose read targets t) z t U := by
  induction t generalizing U with
  | nil=>simp only [population,compatible,List.filter_nil,List.length_nil,Nat.cast_zero,
      fullOutput_nil,sub_self,accrued]
  | node i l r hl hr=>
    rcases ht with ⟨htl,htr,hli,hri,hd⟩
    have heL (V : Domains A B) :
        accrued choose read (charges R choose read targets (.node i l r)) z l V=
        accrued choose read (charges R choose read targets l) z l V := by
      apply accrued_congr
      intro j hj W x
      have hji : j≠i := by intro he; exact hli (he ▸ hj)
      simp only [charges,ite_eq_right hji,ite_eq_left hj]
    have heR (V : Domains A B) :
        accrued choose read (charges R choose read targets (.node i l r)) z r V=
        accrued choose read (charges R choose read targets r) z r V := by
      apply accrued_congr
      intro j hj W x
      have hji : j≠i := by intro he; exact hri (he ▸ hj)
      have hjl : j∉labels l := disjoint_right.mp hd hj
      simp only [charges,ite_eq_right hji,ite_eq_right hjl]
    rw [accrued]
    have hroot : charges R choose read targets (.node i l r) i U (z i)=
        nodeCharge R choose read targets i l r U (z i) := by simp only [charges,ite_true]
    rw [hroot]
    cases hc : choose i (z i) U with
    | none=>
      rw [fullOutput_fail R choose read targets z i l r U hc]
      simp only [nodeCharge,hc,List.length_nil,Nat.cast_zero,sub_zero,add_zero]
    | some c=>
      rw [fullOutput_success R choose read targets z i l r U c hc]
      dsimp only
      rw [heL,heR,←hl _ htl,←hr _ htr]
      simp only [nodeCharge,hc,List.length_append,Nat.cast_add]
      change _-(_+compatible R (read i (z i) U c) (targets i)+_)=_
      ring

variable [Fintype I] [∀ i,Fintype (α i)]

theorem expected_output_loss (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (R : A→B→Prop) (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (budget : I→ℝ) (hb : ∀ i∈labels t,0≤budget i)
    (hlocal : ∀ i∈labels t,∀ V,
      (∑ x,(p i).mass x*charges R choose read targets t i V x)≤budget i) :
    (∑ z,(piLaw p).mass z*(compatible R U (population targets t)-
      (fullOutput R choose read targets z t U).length))≤∑ i∈labels t,budget i := by
  simp_rw [output_loss_eq_accrued R choose read targets _ t U ht]
  exact accrued_expectation p dummy choose read (charges R choose read targets t)
    t U ht budget hb hlocal

end
end SharpLogRamsey.FreshExecution

end

end OAI
