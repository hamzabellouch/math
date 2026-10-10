import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.FreshExecution

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables ChronologicalTree
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

def labels (t : BinaryTree I) : Finset I := (inorder t).toFinset

@[simp] lemma labels_nil : labels (.nil : BinaryTree I)=∅ := rfl

@[simp] lemma labels_node (i : I) (l r : BinaryTree I) :
    labels (.node i l r)=insert i (labels l∪labels r) := by
  ext j
  simp only [labels,inorder,List.mem_toFinset,List.mem_append,List.mem_cons,
    mem_insert,mem_union]
  tauto

def Separated : BinaryTree I→Prop
  | .nil=>True
  | .node i l r=>Separated l ∧ Separated r ∧ i∉labels l ∧ i∉labels r ∧
      Disjoint (labels l) (labels r)

lemma separated_of_nodup (t : BinaryTree I) (h : (inorder t).Nodup) : Separated t := by
  induction t with
  | nil=>trivial
  | node i l r hl hr=>
    simp only [inorder,List.nodup_append,List.nodup_cons] at h
    refine ⟨hl h.1,hr h.2.1.2,?_,?_,?_⟩
    · intro hi
      exact h.2.2 i (by simpa only [labels,List.mem_toFinset] using hi) i (List.mem_cons_self ..) rfl
    · simpa only [labels,List.mem_toFinset] using h.2.1.1
    · apply disjoint_left.mpr
      intro j hj hj'
      exact h.2.2 j (by simpa only [labels,List.mem_toFinset] using hj) j
        (List.mem_cons_of_mem _ (by simpa only [labels,List.mem_toFinset] using hj')) rfl

lemma arrive_absent (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (target : I)
    (t : BinaryTree I) (U : Domains A B) (h : target∉labels t) :
    arrive choose read z target t U=none := by
  induction t generalizing U with
  | nil=>rfl
  | node i l r hl hr=>
    have hi : i≠target := by
      intro he
      apply h
      rw [labels_node,he]
      exact mem_insert_self target _
    have hL : target∉labels l := by intro hj; apply h; simp only [labels_node,mem_insert,mem_union]; tauto
    have hR : target∉labels r := by intro hj; apply h; simp only [labels_node,mem_insert,mem_union]; tauto
    rw [arrive,ite_eq_right hi]
    cases hc : choose i (z i) U with
    | none=>rfl
    | some c=>simp only [hl _ hL,hr _ hR,Option.orElse_none]

def accrued (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (f : ∀ i,Domains A B→α i→ℝ)
    (z : ∀ i,α i) : BinaryTree I→Domains A B→ℝ
  | .nil,_=>0
  | .node i l r,U=>f i U (z i)+match choose i (z i) U with
    | none=>0
    | some c=>
      let V:=read i (z i) U c
      accrued choose read f z l (V.1,U.2)+accrued choose read f z r (U.1,V.2)

lemma produced_root (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (i : I)
    (f : Domains A B→α i→ℝ) (l r : BinaryTree I) (U : Domains A B) :
    produced choose read i f (.node i l r) U z=f U (z i) := by
  simp only [produced,arrive,ite_true]

lemma produced_left (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (i j : I)
    (f : Domains A B→α j→ℝ) (l r : BinaryTree I) (U : Domains A B)
    (hj : j∈labels l) (hi : i∉labels l) (hd : Disjoint (labels l) (labels r))
    (c : C) (hc : choose i (z i) U=some c) :
    produced choose read j f (.node i l r) U z=
      produced choose read j f l ((read i (z i) U c).1,U.2) z := by
  have hij : i≠j := fun he=>hi (he ▸ hj)
  have hnj : j∉labels r := disjoint_left.mp hd hj
  unfold produced
  rw [arrive,ite_eq_right hij,hc]
  dsimp only
  rw [arrive_absent choose read z j r _ hnj]
  cases arrive choose read z j l ((read i (z i) U c).1,U.2) <;> rfl

lemma produced_right (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (i j : I)
    (f : Domains A B→α j→ℝ) (l r : BinaryTree I) (U : Domains A B)
    (hj : j∈labels r) (hi : i∉labels r) (hd : Disjoint (labels l) (labels r))
    (c : C) (hc : choose i (z i) U=some c) :
    produced choose read j f (.node i l r) U z=
      produced choose read j f r (U.1,(read i (z i) U c).2) z := by
  have hij : i≠j := fun he=>hi (he ▸ hj)
  have hnj : j∉labels l := disjoint_right.mp hd hj
  unfold produced
  rw [arrive,ite_eq_right hij,hc]
  dsimp only
  rw [arrive_absent choose read z j l _ hnj]
  rfl

lemma produced_deleted (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (i j : I)
    (f : Domains A B→α j→ℝ) (l r : BinaryTree I) (U : Domains A B)
    (hi : i≠j) (hc : choose i (z i) U=none) :
    produced choose read j f (.node i l r) U z=0 := by
  simp only [produced,arrive,ite_eq_right hi,hc]

theorem accrued_eq_sum (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (f : ∀ i,Domains A B→α i→ℝ)
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B) (ht : Separated t) :
    accrued choose read f z t U=∑ i∈labels t,produced choose read i (f i) t U z := by
  induction t generalizing U with
  | nil=>simp only [accrued,labels_nil,sum_empty]
  | node i l r hl hr=>
    rcases ht with ⟨htl,htr,hli,hri,hd⟩
    rw [labels_node,sum_insert (by simp only [mem_union,not_or]; exact ⟨hli,hri⟩),
      sum_union hd,produced_root,accrued]
    cases hc : choose i (z i) U with
    | none=>
      simp only [add_zero]
      have hzl : (∑ j∈labels l,produced choose read j (f j) (.node i l r) U z)=0 := by
        apply sum_eq_zero
        intro j hj
        exact produced_deleted choose read z i j (f j) l r U (fun he=>hli (he ▸ hj)) hc
      have hzr : (∑ j∈labels r,produced choose read j (f j) (.node i l r) U z)=0 := by
        apply sum_eq_zero
        intro j hj
        exact produced_deleted choose read z i j (f j) l r U (fun he=>hri (he ▸ hj)) hc
      rw [hzl,hzr,add_zero,add_zero]
    | some c=>
      dsimp only
      rw [hl _ htl,hr _ htr]
      congr 1
      exact congrArg₂ (·+·)
        (sum_congr rfl (fun j hj=>(produced_left choose read z i j (f j) l r U hj hli hd c hc).symm))
        (sum_congr rfl (fun j hj=>(produced_right choose read z i j (f j) l r U hj hri hd c hc).symm))

variable [Fintype I] [∀ i,Fintype (α i)]

theorem accrued_expectation (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (f : ∀ i,Domains A B→α i→ℝ)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (budget : I→ℝ) (hb : ∀ i∈labels t,0≤budget i)
    (hlocal : ∀ i∈labels t,∀ V,(∑ x,(p i).mass x*f i V x)≤budget i) :
    (∑ z,(piLaw p).mass z*accrued choose read f z t U)≤∑ i∈labels t,budget i := by
  simp_rw [accrued_eq_sum choose read f _ t U ht,mul_sum]
  rw [sum_comm]
  apply sum_le_sum
  intro i hi
  exact produced_bound p choose read i (dummy i) (f i) t U (budget i) (hb i hi) (hlocal i hi)

end
end SharpLogRamsey.FreshExecution

end

end OAI
