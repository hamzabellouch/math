import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedEndpoint
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedSupportTrim

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] [Fintype I] [Fintype Ω]
  {α : I→Type*} [∀ i,Fintype (α i)]

theorem original_target_loss (μ : Law Ω) (p : ∀ i,Law (α i)) (dummy : ∀ i,α i)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read mask : Ω→∀ i,α i→CapReader A B C)
    (hreadA : ∀ ω i x V c,(read ω i x V c).1=V.1∩(mask ω i x V c).1)
    (hreadB : ∀ ω i x V c,(read ω i x V c).2=V.2∩(mask ω i x V c).2)
    (a : Ω→A) (b : Ω→B) (target : I) (t : BinaryTree I) (U : Domains A B)
    (ht : Separated t) (hmem : target∈labels t)
    (haU : ∀ ω,a ω∈U.1) (hbU : ∀ ω,b ω∈U.2)
    (BA BB : Ω→I→ℝ) (εA εB L : ℝ) (hεA : 0≤εA) (hεB : 0≤εB)
    (hBA : ∀ ω,∀ i∈insert target (leftPath target t),0≤BA ω i)
    (hBB : ∀ ω,∀ i∈insert target (rightPath target t),0≤BB ω i)
    (hlocalA : ∀ ω,∀ i∈insert target (leftPath target t),∀ V,
      (∑ x,(p i).mass x*firstLoss (choose ω) (mask ω) {a ω} i V x)≤BA ω i)
    (hlocalB : ∀ ω,∀ i∈insert target (rightPath target t),∀ V,
      (∑ x,(p i).mass x*secondLoss (choose ω) (mask ω) {b ω} i V x)≤BB ω i)
    (hmeanA : ∀ i∈insert target (leftPath target t),(∑ ω,μ.mass ω*BA ω i)≤εA)
    (hmeanB : ∀ i∈insert target (rightPath target t),(∑ ω,μ.mass ω*BB ω i)≤εB)
    (hdelete : (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      (1-pivotSuccess (choose ω) (read ω) target t U z)))≤L) :
    (∑ ω,μ.mass ω*(∑ z,(piLaw p).mass z*
      targetFailure (choose ω) (read ω) (a ω) (b ω) target t U z))≤
        L+((t.height:ℝ)+1)*(εA+εB) := by
  have hpathA := averaged_path_bound μ p dummy choose read
    (fun ω i=>firstLoss (choose ω) (mask ω) {a ω} i) t U (leftPath target t)
    (fun _=>1) (fun _=>by norm_num) BA
    (fun ω i hi=>hBA ω i (mem_insert_of_mem hi))
    (fun ω i hi=>hlocalA ω i (mem_insert_of_mem hi)) εA
    (fun i hi=>by simpa only [div_one] using hmeanA i (mem_insert_of_mem hi))
  have hpathB := averaged_path_bound μ p dummy choose read
    (fun ω i=>secondLoss (choose ω) (mask ω) {b ω} i) t U (rightPath target t)
    (fun _=>1) (fun _=>by norm_num) BB
    (fun ω i hi=>hBB ω i (mem_insert_of_mem hi))
    (fun ω i hi=>hlocalB ω i (mem_insert_of_mem hi)) εB
    (fun i hi=>by simpa only [div_one] using hmeanB i (mem_insert_of_mem hi))
  have hownA := averaged_path_bound μ p dummy choose read
    (fun ω i=>firstLoss (choose ω) (mask ω) {a ω} i) t U {target}
    (fun _=>1) (fun _=>by norm_num) BA
    (fun ω i hi=>hBA ω i (by rw [mem_singleton.mp hi]; exact mem_insert_self _ _))
    (fun ω i hi=>hlocalA ω i (by rw [mem_singleton.mp hi]; exact mem_insert_self _ _)) εA
    (fun i hi=>by
      have hi' : i=target := mem_singleton.mp hi
      subst i
      simpa only [div_one] using hmeanA target (mem_insert_self _ _))
  have hownB := averaged_path_bound μ p dummy choose read
    (fun ω i=>secondLoss (choose ω) (mask ω) {b ω} i) t U {target}
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
        (∑ j∈leftPath target t,produced (choose ω) (read ω) j
          (firstLoss (choose ω) (mask ω) {a ω} j) t U z)+
        (∑ j∈rightPath target t,produced (choose ω) (read ω) j
          (secondLoss (choose ω) (mask ω) {b ω} j) t U z)+
        produced (choose ω) (read ω) target (firstLoss (choose ω) (mask ω) {a ω} target) t U z+
        produced (choose ω) (read ω) target (secondLoss (choose ω) (mask ω) {b ω} target) t U z)) := by
    apply sum_le_sum
    intro ω _
    apply mul_le_mul_of_nonneg_left _ (μ.nonneg ω)
    apply sum_le_sum
    intro z _
    exact mul_le_mul_of_nonneg_left (target_failure_charge (choose ω) (read ω) (mask ω)
      (hreadA ω) (hreadB ω) z target (a ω) (b ω) t U ht hmem (haU ω) (hbU ω))
      ((piLaw p).nonneg z)
  simp_rw [mul_add,sum_add_distrib] at hpart
  simp_rw [mul_add,sum_add_distrib] at hpart
  linarith

end
end SharpLogRamsey.FreshExecution

end

end OAI
