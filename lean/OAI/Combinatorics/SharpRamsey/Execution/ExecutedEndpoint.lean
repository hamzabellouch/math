import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedDeletion
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedSecondTrim

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

def targetFailure (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (a : A) (b : B) (i : I)
    (t : BinaryTree I) (U : Domains A B) (z : ∀ i,α i) : ℝ :=
  match arrive choose read z i t U with
  | none=>1
  | some V=>match choose i (z i) V with
    | none=>1
    | some c=>if a∈(read i (z i) V c).1 ∧ b∈(read i (z i) V c).2 then 0 else 1

theorem target_failure_charge (choose : ∀ i,α i→Domains A B→Option C)
    (read mask : ∀ i,α i→CapReader A B C)
    (hreadA : ∀ i x V c,(read i x V c).1=V.1∩(mask i x V c).1)
    (hreadB : ∀ i x V c,(read i x V c).2=V.2∩(mask i x V c).2)
    (z : ∀ i,α i) (target : I) (a : A) (b : B)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (haU : a∈U.1) (hbU : b∈U.2) :
    targetFailure choose read a b target t U z≤
      1-pivotSuccess choose read target t U z+
      (∑ j∈leftPath target t,produced choose read j (firstLoss choose mask {a} j) t U z)+
      (∑ j∈rightPath target t,produced choose read j (secondLoss choose mask {b} j) t U z)+
      produced choose read target (firstLoss choose mask {a} target) t U z+
      produced choose read target (secondLoss choose mask {b} target) t U z := by
  have hpA : 0≤∑ j∈leftPath target t,produced choose read j (firstLoss choose mask {a} j) t U z := by
    apply sum_nonneg
    intro j _
    exact produced_nonneg choose read j _ (firstLoss_nonneg choose mask {a} j) t U z
  have hpB : 0≤∑ j∈rightPath target t,produced choose read j (secondLoss choose mask {b} j) t U z := by
    apply sum_nonneg
    intro j _
    exact produced_nonneg choose read j _ (secondLoss_nonneg choose mask {b} j) t U z
  have hoA := produced_nonneg choose read target _ (firstLoss_nonneg choose mask {a} target) t U z
  have hoB := produced_nonneg choose read target _ (secondLoss_nonneg choose mask {b} target) t U z
  cases hv : arrive choose read z target t U with
  | none=>
    have hs : pivotSuccess choose read target t U z=0 := by simp only [pivotSuccess,produced,hv]
    rw [targetFailure,hv,hs]
    linarith
  | some V=>
    cases hc : choose target (z target) V with
    | none=>
      have hs : pivotSuccess choose read target t U z=0 := by
        simp only [pivotSuccess,produced,hv,trialFailure,hc,ite_true,sub_self]
      simp only [targetFailure,hv,hc,hs]
      linarith
    | some c=>
      have hs : pivotSuccess choose read target t U z=1 := by
        simp only [pivotSuccess,produced,hv,trialFailure,hc,Option.some_ne_none,ite_false,sub_zero]
      have hoA' : produced choose read target (firstLoss choose mask {a} target) t U z=
          (({a}\(mask target (z target) V c).1).card:ℝ) := by
        simp only [produced,hv,firstLoss,hc]
      have hoB' : produced choose read target (secondLoss choose mask {b} target) t U z=
          (({b}\(mask target (z target) V c).2).card:ℝ) := by
        simp only [produced,hv,secondLoss,hc]
      have hf:=reached_first_loss choose read mask hreadA z target {a} t U V ht hmem hv
      have hg:=reached_second_loss choose read mask hreadB z target {b} t U V ht hmem hv
      rw [sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr haU),card_empty,Nat.cast_zero,zero_add] at hf
      rw [sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr hbU),card_empty,Nat.cast_zero,zero_add] at hg
      have hcapA : (({a}\(read target (z target) V c).1).card:ℝ)≤
          (({a}\V.1).card:ℝ)+({a}\(mask target (z target) V c).1).card := by
        rw [hreadA]
        exact sdiff_inter_card {a} V.1 _
      have hcapB : (({b}\(read target (z target) V c).2).card:ℝ)≤
          (({b}\V.2).card:ℝ)+({b}\(mask target (z target) V c).2).card := by
        rw [hreadB]
        exact sdiff_inter_card {b} V.2 _
      have hpoint : (if a∈(read target (z target) V c).1 ∧ b∈(read target (z target) V c).2
          then (0:ℝ) else 1)≤
          (({a}\(read target (z target) V c).1).card:ℝ)+({b}\(read target (z target) V c).2).card := by
        have haa : (({a}\(read target (z target) V c).1).card:ℝ) =
            if a∈(read target (z target) V c).1 then 0 else 1 := by
          by_cases ha : a∈(read target (z target) V c).1
          · rw [sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr ha)]
            simp [ha]
          · have he : {a}\(read target (z target) V c).1={a} := by
              ext x
              simp only [mem_sdiff,mem_singleton]
              constructor
              · exact And.left
              · rintro rfl
                exact ⟨rfl,ha⟩
            simp [he,ha]
        have hbb : (({b}\(read target (z target) V c).2).card:ℝ) =
            if b∈(read target (z target) V c).2 then 0 else 1 := by
          by_cases hb : b∈(read target (z target) V c).2
          · rw [sdiff_eq_empty_iff_subset.mpr (singleton_subset_iff.mpr hb)]
            simp [hb]
          · have he : {b}\(read target (z target) V c).2={b} := by
              ext x
              simp only [mem_sdiff,mem_singleton]
              constructor
              · exact And.left
              · rintro rfl
                exact ⟨rfl,hb⟩
            simp [he,hb]
        rw [haa,hbb]
        split_ifs <;> norm_num
        tauto
      simp only [targetFailure,hv,hc,hs,hoA',hoB']
      linarith

end
end SharpLogRamsey.FreshExecution

end

end OAI
