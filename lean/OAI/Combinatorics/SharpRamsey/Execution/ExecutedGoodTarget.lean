import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedTargetBudget

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] {α : I→Type*}

def goodSingleton (good : Prop) (a : A) : Finset A := if good then {a} else ∅

lemma targetFailure_le_one (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (a : A) (b : B) (i : I)
    (t : BinaryTree I) (U : Domains A B) (z : ∀ i,α i) :
    targetFailure choose read a b i t U z≤1 := by
  unfold targetFailure
  split
  · exact le_rfl
  · split
    · exact le_rfl
    · split_ifs <;> norm_num

lemma deletion_nonneg (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (i : I)
    (t : BinaryTree I) (U : Domains A B) (z : ∀ i,α i) :
    0≤1-pivotSuccess choose read i t U z := by
  unfold pivotSuccess produced
  split
  · norm_num
  · dsimp [trialFailure]
    split_ifs <;> norm_num

lemma target_failure_good_charge (choose : ∀ i,α i→Domains A B→Option C)
    (read mask : ∀ i,α i→CapReader A B C)
    (hreadA : ∀ i x V c,(read i x V c).1=V.1∩(mask i x V c).1)
    (hreadB : ∀ i x V c,(read i x V c).2=V.2∩(mask i x V c).2)
    (goodA goodB : Prop) (z : ∀ i,α i) (target : I) (a : A) (b : B)
    (t : BinaryTree I) (U : Domains A B) (ht : Separated t)
    (hmem : target∈labels t) (haU : a∈U.1) (hbU : b∈U.2) :
    targetFailure choose read a b target t U z≤
      1-pivotSuccess choose read target t U z+
      (if goodA then (0:ℝ) else 1)+(if goodB then (0:ℝ) else 1)+
      (∑ j∈leftPath target t,produced choose read j (firstLoss choose mask (goodSingleton goodA a) j) t U z)+
      (∑ j∈rightPath target t,produced choose read j (secondLoss choose mask (goodSingleton goodB b) j) t U z)+
      produced choose read target (firstLoss choose mask (goodSingleton goodA a) target) t U z+
      produced choose read target (secondLoss choose mask (goodSingleton goodB b) target) t U z := by
  by_cases hA : goodA ∧ goodB
  · simpa only [goodSingleton,ite_eq_left hA.1,ite_eq_left hA.2,add_zero] using
      target_failure_charge choose read mask hreadA hreadB z target a b t U ht hmem haU hbU
  · have hbad : (1:ℝ)≤(if goodA then (0:ℝ) else 1)+(if goodB then (0:ℝ) else 1) := by
      split_ifs <;> try norm_num
      tauto
    have hlo := targetFailure_le_one choose read a b target t U z
    have hd := deletion_nonneg choose read target t U z
    have hoA := produced_nonneg choose read target _
      (firstLoss_nonneg choose mask (goodSingleton goodA a) target) t U z
    have hoB := produced_nonneg choose read target _
      (secondLoss_nonneg choose mask (goodSingleton goodB b) target) t U z
    have hpA : 0≤∑ j∈leftPath target t,produced choose read j
        (firstLoss choose mask (goodSingleton goodA a) j) t U z := by
      exact sum_nonneg (fun j _=>produced_nonneg choose read j _
        (firstLoss_nonneg choose mask _ j) t U z)
    have hpB : 0≤∑ j∈rightPath target t,produced choose read j
        (secondLoss choose mask (goodSingleton goodB b) j) t U z := by
      exact sum_nonneg (fun j _=>produced_nonneg choose read j _
        (secondLoss_nonneg choose mask _ j) t U z)
    linarith

variable [Fintype I] [Fintype Ω] [∀ i,Fintype (α i)]

theorem original_good_target_loss (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read mask : Ω→∀ i,α i→CapReader A B C)
    (hreadA : ∀ ω i x V c,(read ω i x V c).1=V.1∩(mask ω i x V c).1)
    (hreadB : ∀ ω i x V c,(read ω i x V c).2=V.2∩(mask ω i x V c).2)
    (goodA goodB : Ω→Prop) (a : Ω→A) (b : Ω→B) (target : I) (t : BinaryTree I) (U : Domains A B)
    (ht : Separated t) (hmem : target∈labels t)
    (haU : ∀ ω,a ω∈U.1) (hbU : ∀ ω,b ω∈U.2)
    (BA BB : Ω→I→ℝ) (εA εB L δA δB : ℝ) (hεA : 0≤εA) (hεB : 0≤εB)
    (hBA : ∀ ω,∀ i∈insert target (leftPath target t),0≤BA ω i)
    (hBB : ∀ ω,∀ i∈insert target (rightPath target t),0≤BB ω i)
    (hlocalA : ∀ ω,∀ i∈insert target (leftPath target t),∀ V,
      (∑ x,(p i).mass x*firstLoss (choose ω) (mask ω) (goodSingleton (goodA ω) (a ω)) i V x)≤BA ω i)
    (hlocalB : ∀ ω,∀ i∈insert target (rightPath target t),∀ V,
      (∑ x,(p i).mass x*secondLoss (choose ω) (mask ω) (goodSingleton (goodB ω) (b ω)) i V x)≤BB ω i)
    (hmeanA : ∀ i∈insert target (leftPath target t),(∑ ω,μ.mass ω*BA ω i)≤εA)
    (hmeanB : ∀ i∈insert target (rightPath target t),(∑ ω,μ.mass ω*BB ω i)≤εB)
    (hbadA : (∑ ω,μ.mass ω*(if goodA ω then (0:ℝ) else 1))≤δA)
    (hbadB : (∑ ω,μ.mass ω*(if goodB ω then (0:ℝ) else 1))≤δB)
    (hdelete : (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (1-pivotSuccess (choose ω) (read ω) target t U z)))≤L) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      targetFailure (choose ω) (read ω) (a ω) (b ω) target t U z))≤
        L+δA+δB+((t.height:ℝ)+1)*(εA+εB) := by
  have hpathA := averaged_path_bound μ p dummy choose read
    (fun ω i=>firstLoss (choose ω) (mask ω) (goodSingleton (goodA ω) (a ω)) i) t U (leftPath target t)
    (fun _=>1) (fun _=>by norm_num) BA
    (fun ω i hi=>hBA ω i (mem_insert_of_mem hi))
    (fun ω i hi=>hlocalA ω i (mem_insert_of_mem hi)) εA
    (fun i hi=>by simpa only [div_one] using hmeanA i (mem_insert_of_mem hi))
  have hpathB := averaged_path_bound μ p dummy choose read
    (fun ω i=>secondLoss (choose ω) (mask ω) (goodSingleton (goodB ω) (b ω)) i) t U (rightPath target t)
    (fun _=>1) (fun _=>by norm_num) BB
    (fun ω i hi=>hBB ω i (mem_insert_of_mem hi))
    (fun ω i hi=>hlocalB ω i (mem_insert_of_mem hi)) εB
    (fun i hi=>by simpa only [div_one] using hmeanB i (mem_insert_of_mem hi))
  have hownA := averaged_path_bound μ p dummy choose read
    (fun ω i=>firstLoss (choose ω) (mask ω) (goodSingleton (goodA ω) (a ω)) i) t U {target}
    (fun _=>1) (fun _=>by norm_num) BA
    (fun ω i hi=>hBA ω i (by rw [mem_singleton.mp hi]; exact mem_insert_self _ _))
    (fun ω i hi=>hlocalA ω i (by rw [mem_singleton.mp hi]; exact mem_insert_self _ _)) εA
    (fun i hi=>by
      have hi' : i=target := mem_singleton.mp hi
      subst i
      simpa only [div_one] using hmeanA target (mem_insert_self _ _))
  have hownB := averaged_path_bound μ p dummy choose read
    (fun ω i=>secondLoss (choose ω) (mask ω) (goodSingleton (goodB ω) (b ω)) i) t U {target}
    (fun _=>1) (fun _=>by norm_num) BB
    (fun ω i hi=>hBB ω i (by rw [mem_singleton.mp hi]; exact mem_insert_self _ _))
    (fun ω i hi=>hlocalB ω i (by rw [mem_singleton.mp hi]; exact mem_insert_self _ _)) εB
    (fun i hi=>by
      have hi' : i=target := mem_singleton.mp hi
      subst i
      simpa only [div_one] using hmeanB target (mem_insert_self _ _))
  simp only [div_one] at hpathA hpathB
  simp only [div_one,sum_singleton,card_singleton,Nat.cast_one,one_mul] at hownA hownB
  have hcA : ((leftPath target t).card:ℝ)*εA≤(t.height:ℝ)*εA :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast leftPath_card target t) hεA
  have hcB : ((rightPath target t).card:ℝ)*εB≤(t.height:ℝ)*εB :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast rightPath_card target t) hεB
  have hpart : (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      targetFailure (choose ω) (read ω) (a ω) (b ω) target t U z))≤
      ∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*(
        1-pivotSuccess (choose ω) (read ω) target t U z+
        (if goodA ω then (0:ℝ) else 1)+(if goodB ω then (0:ℝ) else 1)+
        (∑ j∈leftPath target t,produced (choose ω) (read ω) j
          (firstLoss (choose ω) (mask ω) (goodSingleton (goodA ω) (a ω)) j) t U z)+
        (∑ j∈rightPath target t,produced (choose ω) (read ω) j
          (secondLoss (choose ω) (mask ω) (goodSingleton (goodB ω) (b ω)) j) t U z)+
        produced (choose ω) (read ω) target (firstLoss (choose ω) (mask ω) (goodSingleton (goodA ω) (a ω)) target) t U z+
        produced (choose ω) (read ω) target (secondLoss (choose ω) (mask ω) (goodSingleton (goodB ω) (b ω)) target) t U z)) := by
    apply sum_le_sum
    intro ω _
    apply mul_le_mul_of_nonneg_left _ (μ.nonneg ω)
    apply sum_le_sum
    intro z _
    exact mul_le_mul_of_nonneg_left (target_failure_good_charge (choose ω) (read ω) (mask ω)
      (hreadA ω) (hreadB ω) (goodA ω) (goodB ω) z target (a ω) (b ω) t U ht hmem (haU ω) (hbU ω))
      ((piLaw p).nonneg z)
  simp_rw [mul_add,sum_add_distrib] at hpart
  simp_rw [mul_add,sum_add_distrib] at hpart
  simp only [←sum_mul,(piLaw p).total,one_mul] at hpart
  linarith

end
end SharpLogRamsey.FreshExecution

end

end OAI
