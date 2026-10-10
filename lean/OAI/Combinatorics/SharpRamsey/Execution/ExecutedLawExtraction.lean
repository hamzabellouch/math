import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedExtraction

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] [Fintype I] [Fintype Ω]
  {α : I→Type*} [∀ i,Fintype (α i)]

def sourcePublicLaw (μ : Law Ω) (p : ∀ i,Law (α i)) : Law (Ω×(∀ i,α i)) where
  mass x := μ.mass x.1*(piLaw p).mass x.2
  nonneg x := mul_nonneg (μ.nonneg x.1) ((piLaw p).nonneg x.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [←mul_sum,(piLaw p).total,mul_one,μ.total]

theorem original_output_loss (μ : Law Ω) (p : ∀ i,Law (α i)) (R : A→B→Prop)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C)
    (n : ℕ) (target : Ω→I→Fin n→A×B) (t : BinaryTree I) (U : Domains A B)
    (ht : Separated t)
    (hR : ∀ ω,∀ i∈labels t,∀ j,R (target ω i j).1 (target ω i j).2)
    (δ : ℝ)
    (hpoint : ∀ i∈labels t,∀ j,(∑ ω,μ.mass ω*∑ z,(piLaw p).mass z*
      targetFailure (choose ω) read (target ω i j).1 (target ω i j).2 i t U z)≤δ) :
    (∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*(((labels t).card:ℝ)*n-
      (fullOutput R (choose ω) read (fun i=>List.ofFn (target ω i)) z t U).length))≤
        ((labels t).card:ℝ)*n*δ := by
  have hh := expected_literal_loss (sourcePublicLaw μ p) R (fun x=>choose x.1)
    (fun _=>read) (fun x=>x.2) n (fun x=>target x.1) t U ht (fun x=>hR x.1) δ
    (by
      intro i hi j
      have hp:=hpoint i hi j
      simpa only [sourcePublicLaw,Fintype.sum_prod_type,mul_assoc,←mul_sum] using hp)
  simp only [sourcePublicLaw,Fintype.sum_prod_type,mul_assoc,←mul_sum] at hh
  convert hh using 1
  · simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro ω _
    apply sum_congr rfl
    intro z _
    ring
  · ring

theorem fixed_original_output (μ : Law Ω) (p : ∀ i,Law (α i)) (R : A→B→Prop)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C)
    (n : ℕ) (target : Ω→I→Fin n→A×B) (t : BinaryTree I) (U : Domains A B)
    (ht : Separated t) (hsize : 0<(labels t).card*n)
    (hR : ∀ ω,∀ i∈labels t,∀ j,R (target ω i j).1 (target ω i j).2)
    (hpoint : ∀ i∈labels t,∀ j,(∑ ω,μ.mass ω*∑ z,(piLaw p).mass z*
      targetFailure (choose ω) read (target ω i j).1 (target ω i j).2 i t U z)≤1/4) :
    ∃ z,(1/2:ℝ)≤∑ ω,μ.mass ω*(if (((labels t).card*n:ℕ):ℝ)/2≤
      (fullOutput R (choose ω) read (fun i=>List.ofFn (target ω i)) z t U).length then 1 else 0) := by
  apply fixed_output_half μ p R choose (fun _=>read) (fun ω i=>List.ofFn (target ω i))
    (fun _=>t) U ((labels t).card*n) hsize
  · intro ω
    have hh:=population_length_sum (fun i=>List.ofFn (target ω i)) t ht
    simp only [List.length_ofFn,sum_const,nsmul_eq_mul] at hh
    exact_mod_cast hh
  · have hh:=original_output_loss μ p R choose read n target t U ht hR (1/4) hpoint
    simpa only [Nat.cast_mul,div_eq_mul_inv,one_mul] using hh

end
end SharpLogRamsey.FreshExecution

end

end OAI
