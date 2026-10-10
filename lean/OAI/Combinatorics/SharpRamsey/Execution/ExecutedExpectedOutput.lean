import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedOutputCount

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] [Fintype Ω] {α : I→Type*}

theorem expected_literal_loss (μ : Law Ω) (R : A→B→Prop)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : Ω→∀ i,α i→CapReader A B C) (z : Ω→∀ i,α i)
    (n : ℕ) (target : Ω→I→Fin n→A×B) (t : BinaryTree I) (U : Domains A B)
    (ht : Separated t)
    (hR : ∀ ω,∀ i∈labels t,∀ j,R (target ω i j).1 (target ω i j).2)
    (δ : ℝ)
    (hpoint : ∀ i∈labels t,∀ j,(∑ ω,μ.mass ω*
      targetFailure (choose ω) (read ω) (target ω i j).1 (target ω i j).2 i t U (z ω))≤δ) :
    (∑ ω,μ.mass ω*(((labels t).card:ℝ)*n-
      (fullOutput R (choose ω) (read ω) (fun i=>List.ofFn (target ω i)) (z ω) t U).length))≤
        ((labels t).card:ℝ)*n*δ := by
  have hsize (ω : Ω) :
      ((population (fun i=>List.ofFn (target ω i)) t).length:ℝ)=((labels t).card:ℝ)*n := by
    rw [population_length_sum _ t ht]
    simp only [List.length_ofFn,sum_const,nsmul_eq_mul]
  have he (ω : Ω) : ((labels t).card:ℝ)*n-
      (fullOutput R (choose ω) (read ω) (fun i=>List.ofFn (target ω i)) (z ω) t U).length=
      ∑ i∈labels t,∑ j : Fin n,targetFailure (choose ω) (read ω)
        (target ω i j).1 (target ω i j).2 i t U (z ω) := by
    rw [←hsize ω,output_loss_eq_targets R (choose ω) (read ω) _ (z ω) t U ht]
    · simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
    · intro i hi x hx
      obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hx
      exact hR ω i hi j
  simp_rw [he,mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ i∈labels t,∑ j : Fin n,∑ ω,μ.mass ω*
        targetFailure (choose ω) (read ω) (target ω i j).1 (target ω i j).2 i t U (z ω) := by
      apply sum_congr rfl
      intro i _
      exact sum_comm
    _ ≤ ∑ _i∈labels t,∑ _j : Fin n,δ := by
      apply sum_le_sum
      intro i hi
      exact sum_le_sum (fun j _=>hpoint i hi j)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc]

end
end SharpLogRamsey.FreshExecution

end

end OAI
