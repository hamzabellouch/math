import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.VariableRetention
import OAI.Combinatorics.SharpRamsey.Selection.HistoryLaw

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] [Fintype Ω] {α : I→Type*}

theorem expected_variable_loss (μ : Law Ω) (R : A→B→Prop)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : Ω→∀ i,α i→CapReader A B C) (z : Ω→∀ i,α i)
    (n : I→ℕ) (target : Ω→∀ i,Fin (n i)→A×B) (t : BinaryTree I) (U : Domains A B)
    (ht : Separated t)
    (hR : ∀ ω,∀ i∈labels t,∀ j,R (target ω i j).1 (target ω i j).2)
    (δ : ℝ)
    (hpoint : ∀ i∈labels t,∀ j,(∑ ω,μ.mass ω*
      targetFailure (choose ω) (read ω) (target ω i j).1 (target ω i j).2 i t U (z ω))≤δ) :
    (∑ ω,μ.mass ω*((∑ i∈labels t,(n i:ℝ))-
      (fullOutput R (choose ω) (read ω) (fun i=>List.ofFn (target ω i)) (z ω) t U).length))≤
        (∑ i∈labels t,(n i:ℝ))*δ := by
  have hsize (ω : Ω) :
      ((population (fun i=>List.ofFn (target ω i)) t).length:ℝ)=∑ i∈labels t,(n i:ℝ) := by
    rw [population_length_sum _ t ht]
    simp only [List.length_ofFn]
  have he (ω : Ω) : (∑ i∈labels t,(n i:ℝ))-
      (fullOutput R (choose ω) (read ω) (fun i=>List.ofFn (target ω i)) (z ω) t U).length=
      ∑ i∈labels t,∑ j : Fin (n i),targetFailure (choose ω) (read ω)
        (target ω i j).1 (target ω i j).2 i t U (z ω) := by
    rw [←hsize ω,output_loss_eq_targets R (choose ω) (read ω) _ (z ω) t U ht]
    · simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
    · intro i hi x hx
      obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hx
      exact hR ω i hi j
  simp_rw [he,mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ i∈labels t,∑ j : Fin (n i),∑ ω,μ.mass ω*
        targetFailure (choose ω) (read ω) (target ω i j).1 (target ω i j).2 i t U (z ω) := by
      apply sum_congr rfl
      intro i _
      exact sum_comm
    _ ≤ ∑ i∈labels t,∑ _j : Fin (n i),δ := by
      apply sum_le_sum
      intro i hi
      exact sum_le_sum (fun j _=>hpoint i hi j)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,sum_mul]

variable [Fintype I] [∀ i,Fintype (α i)]

theorem original_variable_loss (μ : Law Ω) (p : ∀ i,Law (α i)) (R : A→B→Prop)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C)
    (n : I→ℕ) (target : Ω→∀ i,Fin (n i)→A×B) (t : BinaryTree I) (U : Domains A B)
    (ht : Separated t)
    (hR : ∀ ω,∀ i∈labels t,∀ j,R (target ω i j).1 (target ω i j).2)
    (δ : ℝ)
    (hpoint : ∀ i∈labels t,∀ j,(∑ ω,μ.mass ω*∑ z,(piLaw p).mass z*
      targetFailure (choose ω) read (target ω i j).1 (target ω i j).2 i t U z)≤δ) :
    (∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*((∑ i∈labels t,(n i:ℝ))-
      (fullOutput R (choose ω) read (fun i=>List.ofFn (target ω i)) z t U).length))≤
        (∑ i∈labels t,(n i:ℝ))*δ := by
  have hh:=expected_variable_loss (sourcePublicLaw μ p) R (fun x=>choose x.1)
    (fun _=>read) (fun x=>x.2) n (fun x=>target x.1) t U ht (fun x=>hR x.1) δ
    (by
      intro i hi j
      have hp:=hpoint i hi j
      simpa only [sourcePublicLaw,Fintype.sum_prod_type,mul_assoc,←mul_sum] using hp)
  simp only [sourcePublicLaw,Fintype.sum_prod_type,mul_assoc,←mul_sum] at hh
  convert hh using 1
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  apply sum_congr rfl
  intro z _
  ring

end
end SharpLogRamsey.FreshExecution

end

end OAI
