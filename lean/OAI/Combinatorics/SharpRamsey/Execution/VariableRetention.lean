import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedLawExtraction

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] {α : I→Type*}
variable [Fintype Ω] [Fintype I] [∀ i,Fintype (α i)]

theorem fixed_output_half_le (μ : Law Ω) (p : ∀ i,Law (α i)) (R : A→B→Prop)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : Ω→∀ i,α i→CapReader A B C) (targets : Ω→I→List (A×B))
    (t : Ω→BinaryTree I) (U : Domains A B) (N : ℕ) (hN : 0<N)
    (hsize : ∀ ω,(population (targets ω) (t ω)).length≤N)
    (hmean : (∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*((N:ℝ)-
      (fullOutput R (choose ω) (read ω) (targets ω) z (t ω) U).length))≤(N:ℝ)/4) :
    ∃ z,(1/2:ℝ)≤∑ ω,μ.mass ω*(if (N:ℝ)/2≤
      (fullOutput R (choose ω) (read ω) (targets ω) z (t ω) U).length then 1 else 0) := by
  let out := fun ω z => (fullOutput R (choose ω) (read ω) (targets ω) z (t ω) U).length
  have hbound (ω : Ω) (z : ∀ i,α i) : out ω z≤N := by
    exact (fullOutput_sublist R (choose ω) (read ω) (targets ω) z (t ω) U).length_le.trans (hsize ω)
  have hp (ω : Ω) (z : ∀ i,α i) :
      (N:ℝ)/2-((N:ℝ)-out ω z)≤(N:ℝ)/2*(if (N:ℝ)/2≤out ω z then 1 else 0) := by
    split_ifs with hh
    · have hb : (out ω z:ℝ)≤N := by exact_mod_cast hbound ω z
      linarith
    · linarith
  have hz (z : ∀ i,α i) :
      (N:ℝ)/2-(∑ ω,μ.mass ω*((N:ℝ)-out ω z))≤
        (N:ℝ)/2*(∑ ω,μ.mass ω*(if (N:ℝ)/2≤out ω z then 1 else 0)) := by
    have hh:=sum_le_sum (fun ω (_ : ω∈univ)=>mul_le_mul_of_nonneg_left (hp ω z) (μ.nonneg ω))
    simpa only [mul_sub,sum_sub_distrib,←sum_mul,μ.total,one_mul,mul_left_comm,mul_sum] using hh
  have hall:=sum_le_sum (fun z (_ : z∈univ)=>mul_le_mul_of_nonneg_left (hz z) ((piLaw p).nonneg z))
  have hall' : (N:ℝ)/2-(∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*((N:ℝ)-out ω z))≤
      (N:ℝ)/2*(∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*(if (N:ℝ)/2≤out ω z then 1 else 0)) := by
    simpa only [mul_sub,sum_sub_distrib,←sum_mul,(piLaw p).total,one_mul,mul_left_comm,mul_sum] using hall
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hs : (1/2:ℝ)≤∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*(if (N:ℝ)/2≤out ω z then 1 else 0) := by
    change (∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*((N:ℝ)-out ω z))≤(N:ℝ)/4 at hmean
    nlinarith
  exact exists_fixed_family μ p (fun ω z=>(N:ℝ)/2≤out ω z) (1/2) hs

theorem fixed_output_of_budgets (μ : Law Ω) (p : ∀ i,Law (α i)) (R : A→B→Prop)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : Ω→∀ i,α i→CapReader A B C) (targets : Ω→I→List (A×B))
    (t : Ω→BinaryTree I) (U : Domains A B) (N : ℕ) (hN : 0<N)
    (hsize : ∀ ω,(population (targets ω) (t ω)).length≤N)
    (e₁ e₂ : ℝ) (he : e₁+e₂≤(N:ℝ)/4)
    (hdel : (∑ ω,μ.mass ω*((N:ℝ)-(population (targets ω) (t ω)).length))≤e₁)
    (hdecode : (∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*
      (((population (targets ω) (t ω)).length:ℝ)-
      (fullOutput R (choose ω) (read ω) (targets ω) z (t ω) U).length))≤e₂) :
    ∃ z,(1/2:ℝ)≤∑ ω,μ.mass ω*(if (N:ℝ)/2≤
      (fullOutput R (choose ω) (read ω) (targets ω) z (t ω) U).length then 1 else 0) := by
  apply fixed_output_half_le μ p R choose read targets t U N hN hsize
  calc
    _ = (∑ ω,μ.mass ω*((N:ℝ)-(population (targets ω) (t ω)).length))+
        (∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*
          (((population (targets ω) (t ω)).length:ℝ)-
          (fullOutput R (choose ω) (read ω) (targets ω) z (t ω) U).length)) := by
      have heq (ω : Ω) (z : ∀ i,α i) :
          (N:ℝ)-(fullOutput R (choose ω) (read ω) (targets ω) z (t ω) U).length =
          ((N:ℝ)-(population (targets ω) (t ω)).length)+
          (((population (targets ω) (t ω)).length:ℝ)-
          (fullOutput R (choose ω) (read ω) (targets ω) z (t ω) U).length) := by ring
      simp_rw [heq,mul_add,sum_add_distrib]
      simp only [mul_add,sum_add_distrib]
      rw [←sum_mul,(piLaw p).total,one_mul]
    _ ≤ e₁+e₂ := add_le_add hdel hdecode
    _ ≤ _ := he

end
end SharpLogRamsey.FreshExecution

end

end OAI
