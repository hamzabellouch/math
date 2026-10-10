import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.TreeMessageEntropy
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedCosts

namespace OAI

section
namespace SharpLogRamsey.ExecutedPotential
open Finset Real BinaryTree TreeDecoder TreeCodeEntropy
open scoped Classical
noncomputable section
variable {A B C I Ω : Type*}

def codeTree (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (t : BinaryTree I) (U : Domains A B) : BinaryTree C :=
  (execute read choose t U).map Prod.snd

lemma codeTree_numNodes (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (t : BinaryTree I) (U : Domains A B) : (codeTree read choose t U).numNodes≤t.numNodes := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    simp only [codeTree,execute]
    split
    · simp only [BinaryTree.map,numNodes]; omega
    · simp only [BinaryTree.map,numNodes]
      exact Nat.add_le_add_right (Nat.add_le_add (hl _) (hr _)) 1

lemma codeTree_mem (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (choose : I→Domains A B→Option C)
    (hallowed : ∀ i U c,choose i U=some c→c∈allowed U)
    (t : BinaryTree I) (U : Domains A B) :
    codeTree read choose t U∈codes allowed read (shape (codeTree read choose t U)) U := by
  induction t generalizing U with
  | nil => simp [codeTree,execute,shape,BinaryTree.map,codes]
  | node i l r hl hr =>
    simp only [codeTree,execute]
    split
    · simp [shape,BinaryTree.map,codes]
    · rename_i c hc
      simp only [BinaryTree.map,shape,codes]
      apply mem_biUnion.mpr
      refine ⟨c,hallowed i U c hc,mem_image.mpr ?_⟩
      exact ⟨(_, _),mem_product.mpr ⟨hl _,hr _⟩,rfl⟩

lemma codeTree_cost (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (choose : I→Domains A B→Option C) (t : BinaryTree I) (U : Domains A B) :
    TreeCodeEntropy.cost allowed read (codeTree read choose t U) U=
      TreePotential.total (fun z : I×Domains A B×C=>log (allowed z.2.1).card)
        (annotate read choose t U) := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    cases hj : choose i U with
    | none => simp only [codeTree,execute,annotate,hj,BinaryTree.map,TreeCodeEntropy.cost,
        TreePotential.total]
    | some c =>
      simp only [codeTree,execute,annotate,hj,BinaryTree.map,TreeCodeEntropy.cost,
        TreePotential.total]
      exact congrArg₂ (fun x y=>log (allowed U).card+x+y) (hl _) (hr _)

theorem codeTree_cost_bound (Q C₀ b c P : ℝ) (hQ : 0<Q) (hC : 1≤C₀) (hb : 0≤b)
    (hc : 0≤c) (hP : 0≤P) (N H : ℕ)
    (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (choose : I→Domains A B→Option C)
    (hvalid : ∀ i U x,choose i U=some x→
      ∃ S : Finset A,∃ T : Finset B,S.Nonempty ∧ T.Nonempty ∧
      (9/10:ℝ)*S.card≤(S∩U.1).card ∧ (9/10:ℝ)*T.card≤(T∩U.2).card ∧
      Q*exp (-b)≤(S.card:ℝ)*T.card ∧
      ((read U x).1.card:ℝ)≤C₀*Q/T.card ∧ ((read U x).2.card:ℝ)≤C₀*Q/S.card)
    (hcost : ∀ i U x,choose i U=some x→log (allowed U).card≤c*(potential Q U+P))
    (t : BinaryTree I) (hN : t.numNodes≤N) (hH : t.height≤H) (U : Domains A B) :
    TreeCodeEntropy.cost allowed read (codeTree read choose t U) U≤
      c*((H:ℝ)*(potential Q U+(N:ℝ)*(b+log 4+2*log C₀))+(N:ℝ)*P) := by
  rw [codeTree_cost]
  apply (maximum_cost Q C₀ b c P hQ hC hb hc hP read choose hvalid
    (fun _ U _=>log (allowed U).card) hcost t U).trans
  have hK : 0≤b+log 4+2*log C₀ := add_nonneg
    (add_nonneg hb (log_nonneg (by norm_num)))
    (mul_nonneg (by norm_num) (log_nonneg hC))
  have hn : (t.numNodes:ℝ)≤N := by exact_mod_cast hN
  have hh : (t.height:ℝ)≤H := by exact_mod_cast hH
  apply mul_le_mul_of_nonneg_left _ hc
  apply add_le_add _ (mul_le_mul_of_nonneg_right hn hP)
  apply mul_le_mul hh (add_le_add le_rfl (mul_le_mul_of_nonneg_right hn hK))
  · exact add_nonneg (potential_nonneg Q U) (mul_nonneg (by positivity) hK)
  · positivity

variable [Fintype Ω]

theorem execution_entropy (p : Selection.Law Ω)
    (Q C₀ b c P : ℝ) (hQ : 0<Q) (hC : 1≤C₀) (hb : 0≤b) (hc : 0≤c) (hP : 0≤P)
    (N H : ℕ) (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (choose : Ω→I→Domains A B→Option C) (t : Ω→BinaryTree I) (U : Domains A B)
    (hN : ∀ ω,(t ω).numNodes≤N) (hH : ∀ ω,(t ω).height≤H)
    (hallowed : ∀ ω i U x,choose ω i U=some x→x∈allowed U)
    (hvalid : ∀ ω i U x,choose ω i U=some x→
      ∃ S : Finset A,∃ T : Finset B,S.Nonempty ∧ T.Nonempty ∧
      (9/10:ℝ)*S.card≤(S∩U.1).card ∧ (9/10:ℝ)*T.card≤(T∩U.2).card ∧
      Q*exp (-b)≤(S.card:ℝ)*T.card ∧
      ((read U x).1.card:ℝ)≤C₀*Q/T.card ∧ ((read U x).2.card:ℝ)≤C₀*Q/S.card)
    (hcost : ∀ ω i U x,choose ω i U=some x→log (allowed U).card≤c*(potential Q U+P)) :
    let M := fun ω=>codeTree read (choose ω) (t ω) U
    let R := univ.image M
    let msg : Ω→R := fun ω=>⟨M ω,mem_image.mpr ⟨ω,mem_univ _,rfl⟩⟩
    Selection.entropy (p.map msg)≤((2*N+1:ℕ):ℝ)*log 2+
      c*((H:ℝ)*(potential Q U+(N:ℝ)*(b+log 4+2*log C₀))+(N:ℝ)*P) := by
  dsimp only
  apply tree_message_entropy _ allowed read U Subtype.val Subtype.val_injective N
  · intro g
    obtain ⟨ω,hω,he⟩ := mem_image.mp g.property
    rw [←he]
    exact (codeTree_numNodes read (choose ω) (t ω) U).trans (hN ω)
  · intro g
    obtain ⟨ω,hω,he⟩ := mem_image.mp g.property
    rw [←he]
    exact codeTree_mem allowed read (choose ω) (hallowed ω) (t ω) U
  · intro g
    obtain ⟨ω,hω,he⟩ := mem_image.mp g.property
    rw [←he]
    exact codeTree_cost_bound Q C₀ b c P hQ hC hb hc hP N H allowed read
      (choose ω) (hvalid ω) (hcost ω) (t ω) (hN ω) (hH ω) U

end
end SharpLogRamsey.ExecutedPotential

end

end OAI
