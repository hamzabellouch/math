import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedConditioning

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] {α : I→Type*}

def fullMessage (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B) : BinaryTree ((I×C)×ℕ) :=
  message R (fixedRead read z) targets (fun i=>(targets i).length)
    (execute (fixedRead read z) (fixedChoose choose z) t U) U

omit [DecidableEq I] in
lemma prefix_decoder_correct (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B) (m : ℕ) :
    List.Forall₂ (fun x D=>x∈D)
      ((fullOutput R choose read targets z t U).take m)
      ((decode R (fixedRead read z) (fullMessage R choose read targets z t U) U).take m) := by
  exact List.forall₂_take m (decoder_correct R (fixedRead read z) targets
    (fun i=>(targets i).length) (execute (fixedRead read z) (fixedChoose choose z) t U) U)

variable [Fintype Ω] [Fintype I] [∀ i,Fintype (α i)]

theorem fixed_extraction (μ : Law Ω) (p : ∀ i,Law (α i)) (R : A→B→Prop)
    (choose : Ω→∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : Ω→I→List (A×B))
    (t : Ω→BinaryTree I) (U : Domains A B) (N : ℕ) (hN : 0<N)
    (hsize : ∀ ω,(population (targets ω) (t ω)).length=N)
    (Q : (A×B)→(A×B)→Prop)
    (hcons : ∀ ω,μ.mass ω≠0→(population (targets ω) (t ω)).Pairwise Q)
    (hmean : (∑ z,(piLaw p).mass z*∑ ω,μ.mass ω*((N:ℝ)-
      (fullOutput R (choose ω) read (targets ω) z (t ω) U).length))≤(N:ℝ)/4) :
    ∃ z,let E:=fun ω=>(N:ℝ)/2≤(fullOutput R (choose ω) read (targets ω) z (t ω) U).length
      ∃ hE : 0<acceptProb μ E,
        (1/2:ℝ)≤acceptProb μ E ∧
        ∀ ω,(conditionSuccess μ E hE).mass ω≠0→
          let out:=(fullOutput R (choose ω) read (targets ω) z (t ω) U).take (N/2)
          out.length=N/2 ∧ List.Sublist out (population (targets ω) (t ω)) ∧ out.Pairwise Q ∧
          List.Forall₂ (fun x D=>x∈D) out
            ((decode R (fixedRead read z) (fullMessage R (choose ω) read (targets ω) z (t ω) U) U).take (N/2)) := by
  obtain ⟨z,hz⟩:=fixed_output_half μ p R choose (fun _=>read) targets t U N hN hsize hmean
  let E:=fun ω=>(N:ℝ)/2≤(fullOutput R (choose ω) read (targets ω) z (t ω) U).length
  have he : (1/2:ℝ)≤acceptProb μ E := by
    convert hz using 1
    simp only [acceptProb,accepted]
    apply sum_congr rfl
    intro ω _
    split_ifs <;> simp only [mul_zero,mul_one]
  have hp : 0<acceptProb μ E := lt_of_lt_of_le (by norm_num) he
  refine ⟨z,hp,he,?_⟩
  intro ω hω
  obtain ⟨hμ,hE⟩:=conditionSuccess_support μ E hp ω hω
  have hlen : N/2≤(fullOutput R (choose ω) read (targets ω) z (t ω) U).length := by
    have hh : (N:ℝ)≤2*(fullOutput R (choose ω) read (targets ω) z (t ω) U).length := by
      dsimp only [E] at hE
      simpa only [mul_comm] using (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mp hE
    have hh' : N≤2*(fullOutput R (choose ω) read (targets ω) z (t ω) U).length := by exact_mod_cast hh
    omega
  have hsub:= (List.take_sublist (N/2) (fullOutput R (choose ω) read (targets ω) z (t ω) U)).trans
    (fullOutput_sublist R (choose ω) read (targets ω) z (t ω) U)
  exact ⟨List.length_take_of_le hlen,hsub,List.Pairwise.sublist hsub (hcons ω hμ),
    prefix_decoder_correct R (choose ω) read (targets ω) z (t ω) U (N/2)⟩

end
end SharpLogRamsey.FreshExecution

end

end OAI
