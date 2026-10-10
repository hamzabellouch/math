import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.ChronologicalTree
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedPotential

namespace OAI

section
namespace SharpLogRamsey.ExecutedPotential
open Finset Real BinaryTree TreeDecoder
open scoped Classical
noncomputable section
variable {A B I C : Type*}

lemma total_cost_local (Q c P : ℝ) (read : CapReader A B C)
    (choose : I→Domains A B→Option C) (cost : I→Domains A B→C→ℝ)
    (hcost : ∀ i U x,choose i U=some x → cost i U x≤c*(potential Q U+P))
    (t : BinaryTree I) (U : Domains A B) :
    TreePotential.total (fun z : I×Domains A B×C => cost z.1 z.2.1 z.2.2)
      (annotate read choose t U)≤
      c*(TreePotential.total (fun z : I×Domains A B×C => potential Q z.2.1)
        (annotate read choose t U)+((annotate read choose t U).numNodes:ℝ)*P) := by
  induction t generalizing U with
  | nil => simp [annotate,TreePotential.total]
  | node i l r hl hr =>
    simp only [annotate]
    split
    · simp [TreePotential.total]
    · rename_i x hx
      have h := hcost i U x hx
      have hl' := hl ((read U x).1,U.2)
      have hr' := hr (U.1,(read U x).2)
      simp only [TreePotential.total,numNodes,Nat.cast_add,Nat.cast_one]
      linarith

theorem maximum_cost (Q C₀ b c P : ℝ) (hQ : 0<Q) (hC : 1≤C₀) (hb : 0≤b)
    (hc : 0≤c) (hP : 0≤P)
    (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (hvalid : ∀ i U x, choose i U=some x →
      ∃ S : Finset A, ∃ T : Finset B, S.Nonempty ∧ T.Nonempty ∧
      (9/10:ℝ)*S.card≤(S∩U.1).card ∧ (9/10:ℝ)*T.card≤(T∩U.2).card ∧
      Q*exp (-b)≤(S.card:ℝ)*T.card ∧
      ((read U x).1.card:ℝ)≤C₀*Q/T.card ∧ ((read U x).2.card:ℝ)≤C₀*Q/S.card)
    (cost : I→Domains A B→C→ℝ)
    (hcost : ∀ i U x,choose i U=some x → cost i U x≤c*(potential Q U+P))
    (t : BinaryTree I) (U : Domains A B) :
    TreePotential.total (fun z : I×Domains A B×C => cost z.1 z.2.1 z.2.2)
      (annotate read choose t U)≤
      c*((t.height:ℝ)*(potential Q U+(t.numNodes:ℝ)*(b+log 4+2*log C₀))+
        (t.numNodes:ℝ)*P) := by
  let K := b+log 4+2*log C₀
  have hK : 0≤K := add_nonneg (add_nonneg hb (log_nonneg (by norm_num)))
    (mul_nonneg (by norm_num) (log_nonneg hC))
  have ha := admissible Q C₀ b hQ hC read choose hvalid t U
  have ht := TreePotential.total_le_height _ K hK _ ha
  have hr := root_le Q read choose t U
  have hh : ((annotate read choose t U).height:ℝ)≤t.height := by
    exact_mod_cast annotate_height read choose t U
  have hn : ((annotate read choose t U).numNodes:ℝ)≤t.numNodes := by
    exact_mod_cast annotate_numNodes read choose t U
  apply (total_cost_local Q c P read choose cost hcost t U).trans
  apply mul_le_mul_of_nonneg_left _ hc
  apply add_le_add _ (mul_le_mul_of_nonneg_right hn hP)
  apply ht.trans
  apply mul_le_mul hh (add_le_add hr (mul_le_mul_of_nonneg_right hn hK))
  · exact add_nonneg (TreePotential.root_nonneg _ K ha) (mul_nonneg (by positivity) hK)
  · positivity

end
end SharpLogRamsey.ExecutedPotential

end

end OAI
