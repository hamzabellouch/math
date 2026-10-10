import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedTrim

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

def plannedPath (target : I) : BinaryTree I→Finset I
  | .nil=>∅
  | .node i l r=>if i=target then {i} else
      insert i (if target∈labels l then plannedPath target l else plannedPath target r)

lemma plannedPath_subset (target : I) (t : BinaryTree I) : plannedPath target t⊆labels t := by
  induction t with
  | nil=>exact empty_subset _
  | node i l r hl hr=>
    rw [plannedPath,labels_node]
    split_ifs with hi hj
    · exact singleton_subset_iff.mpr (mem_insert_self _ _)
    · exact insert_subset_insert i (hl.trans subset_union_left)
    · exact insert_subset_insert i (hr.trans subset_union_right)

lemma plannedPath_card (target : I) (t : BinaryTree I) :
    (plannedPath target t).card≤t.height := by
  induction t with
  | nil=>rfl
  | node i l r hl hr=>
    rw [plannedPath]
    split_ifs
    · simp only [card_singleton,height]; omega
    · exact (card_insert_le _ _).trans (by simp only [height]; omega)
    · exact (card_insert_le _ _).trans (by simp only [height]; omega)

def trialFailure (choose : ∀ i,α i→Domains A B→Option C)
    (i : I) (V : Domains A B) (x : α i) : ℝ := if choose i x V=none then 1 else 0

def pivotSuccess (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (target : I)
    (t : BinaryTree I) (U : Domains A B) (z : ∀ i,α i) : ℝ :=
  produced choose read target (fun V x=>1-trialFailure choose target V x) t U z

theorem deletion_eq_path (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (target : I)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) :
    1-pivotSuccess choose read target t U z=
      ∑ j∈plannedPath target t,produced choose read j (trialFailure choose j) t U z := by
  induction t generalizing U with
  | nil=>simp [labels_nil] at hmem
  | node i l r hl hr=>
    rcases ht with ⟨htl,htr,hli,hri,hd⟩
    by_cases hi : i=target
    · subst target
      rw [plannedPath,ite_eq_left rfl,sum_singleton,produced_root,pivotSuccess,produced_root]
      ring
    · rw [plannedPath,ite_eq_right hi]
      by_cases hL : target∈labels l
      · rw [ite_eq_left hL,sum_insert (fun hj=>hli (plannedPath_subset target l hj)),produced_root]
        cases hc : choose i (z i) U with
        | none=>
          rw [pivotSuccess,produced_deleted choose read z i target _ l r U hi hc]
          have hzero : (∑ j∈plannedPath target l,
              produced choose read j (trialFailure choose j) (.node i l r) U z)=0 := by
            apply sum_eq_zero
            intro j hj
            exact produced_deleted choose read z i j _ l r U
              (fun he=>hli (he ▸ plannedPath_subset target l hj)) hc
          rw [hzero]
          simp only [trialFailure,hc,ite_true,sub_zero,add_zero]
        | some c=>
          rw [pivotSuccess,produced_left choose read z i target _ l r U hL hli hd c hc]
          have he : (∑ j∈plannedPath target l,
              produced choose read j (trialFailure choose j) (.node i l r) U z)=
              ∑ j∈plannedPath target l,produced choose read j (trialFailure choose j)
                l ((read i (z i) U c).1,U.2) z := by
            apply sum_congr rfl
            intro j hj
            exact produced_left choose read z i j _ l r U
              (plannedPath_subset target l hj) hli hd c hc
          rw [he]
          simp only [trialFailure,hc,Option.some_ne_none,ite_false,zero_add]
          exact hl _ htl hL
      · have hR : target∈labels r := by
          rw [labels_node,mem_insert,mem_union] at hmem
          rcases hmem with he|he|he
          · exact False.elim (hi he.symm)
          · exact False.elim (hL he)
          · exact he
        rw [ite_eq_right hL,sum_insert (fun hj=>hri (plannedPath_subset target r hj)),produced_root]
        cases hc : choose i (z i) U with
        | none=>
          rw [pivotSuccess,produced_deleted choose read z i target _ l r U hi hc]
          have hzero : (∑ j∈plannedPath target r,
              produced choose read j (trialFailure choose j) (.node i l r) U z)=0 := by
            apply sum_eq_zero
            intro j hj
            exact produced_deleted choose read z i j _ l r U
              (fun he=>hri (he ▸ plannedPath_subset target r hj)) hc
          rw [hzero]
          simp only [trialFailure,hc,ite_true,sub_zero,add_zero]
        | some c=>
          rw [pivotSuccess,produced_right choose read z i target _ l r U hR hri hd c hc]
          have he : (∑ j∈plannedPath target r,
              produced choose read j (trialFailure choose j) (.node i l r) U z)=
              ∑ j∈plannedPath target r,produced choose read j (trialFailure choose j)
                r (U.1,(read i (z i) U c).2) z := by
            apply sum_congr rfl
            intro j hj
            exact produced_right choose read z i j _ l r U
              (plannedPath_subset target r hj) hri hd c hc
          rw [he]
          simp only [trialFailure,hc,Option.some_ne_none,ite_false,zero_add]
          exact hr _ htr hR

variable [Fintype I] [∀ i,Fintype (α i)]

theorem expected_deletion (p : ∀ i,Law (α i))
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (target : I)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (δ : ℝ) (hδ : 0≤δ)
    (hlocal : ∀ j∈plannedPath target t,
      (∑ z,(piLaw p).mass z*produced choose read j (trialFailure choose j) t U z)≤δ) :
    (∑ z,(piLaw p).mass z*(1-pivotSuccess choose read target t U z))≤t.height*δ := by
  simp_rw [deletion_eq_path choose read _ target t U ht hmem,mul_sum]
  rw [sum_comm]
  calc
    _ ≤ ∑ j∈plannedPath target t,δ := sum_le_sum (fun j hj=>hlocal j hj)
    _ = ((plannedPath target t).card:ℝ)*δ := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast plannedPath_card target t) hδ

theorem expected_deletion_quadratic (p : ∀ i,Law (α i))
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (target : I)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (a b : ℝ) (ha : 0≤a) (hb : 0≤b)
    (hlocal : ∀ j∈plannedPath target t,
      (∑ z,(piLaw p).mass z*produced choose read j (trialFailure choose j) t U z)≤a*t.height+b) :
    (∑ z,(piLaw p).mass z*(1-pivotSuccess choose read target t U z))≤a*t.height^2+b*t.height := by
  have h:=expected_deletion p choose read target t U ht hmem (a*t.height+b)
    (add_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) hb) hlocal
  nlinarith

end
end SharpLogRamsey.FreshExecution

end

end OAI
