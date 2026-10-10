import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedFullMessage

namespace OAI

section
namespace SharpLogRamsey.TreePotential
open BinaryTree
lemma total_sub_const {α : Type*} (f : α→ℝ) (D : ℝ) (t : BinaryTree α) :
    total (fun a=>f a-D) t=total f t-(t.numNodes:ℝ)*D := by
  induction t with
  | nil=>simp [total]
  | node a l r hl hr=>simp only [total,numNodes,Nat.cast_add,Nat.cast_one,hl,hr]; ring
end SharpLogRamsey.TreePotential

namespace SharpLogRamsey.ExecutedPotential
open Finset Real BinaryTree TreeDecoder TreeCodeEntropy
open scoped Classical
noncomputable section
variable {A B C I Ω : Type*}

theorem codeTree_cost_overhead (Q C₀ b c P D : ℝ) (hQ : 0<Q) (hC : 1≤C₀) (hb : 0≤b)
    (hc : 0≤c) (hP : 0≤P) (hD : 0≤D) (N H : ℕ)
    (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (choose : I→Domains A B→Option C)
    (hvalid : ∀ i U x,choose i U=some x→
      ∃ S : Finset A,∃ T : Finset B,S.Nonempty ∧ T.Nonempty ∧
      (9/10:ℝ)*S.card≤(S∩U.1).card ∧ (9/10:ℝ)*T.card≤(T∩U.2).card ∧
      Q*exp (-b)≤(S.card:ℝ)*T.card ∧
      ((read U x).1.card:ℝ)≤C₀*Q/T.card ∧ ((read U x).2.card:ℝ)≤C₀*Q/S.card)
    (hcost : ∀ i U x,choose i U=some x→log (allowed U).card≤D+c*(potential Q U+P))
    (t : BinaryTree I) (hN : t.numNodes≤N) (hH : t.height≤H) (U : Domains A B) :
    TreeCodeEntropy.cost allowed read (codeTree read choose t U) U≤
      (N:ℝ)*D+c*((H:ℝ)*(potential Q U+(N:ℝ)*(b+log 4+2*log C₀))+(N:ℝ)*P) := by
  have hx := maximum_cost Q C₀ b c P hQ hC hb hc hP read choose hvalid
    (fun _ V _=>log (allowed V).card-D) (by intro i V x hx; linarith [hcost i V x hx]) t U
  rw [TreePotential.total_sub_const] at hx
  have hn₀ : ((annotate read choose t U).numNodes:ℝ)≤N := by
    exact_mod_cast (annotate_numNodes read choose t U).trans hN
  have hn : (t.numNodes:ℝ)≤N := by exact_mod_cast hN
  have hh : (t.height:ℝ)≤H := by exact_mod_cast hH
  have hK : 0≤b+log 4+2*log C₀ := add_nonneg
    (add_nonneg hb (log_nonneg (by norm_num))) (mul_nonneg (by norm_num) (log_nonneg hC))
  have hupper : c*((t.height:ℝ)*(potential Q U+(t.numNodes:ℝ)*(b+log 4+2*log C₀))+(t.numNodes:ℝ)*P)≤
      c*((H:ℝ)*(potential Q U+(N:ℝ)*(b+log 4+2*log C₀))+(N:ℝ)*P) := by
    apply mul_le_mul_of_nonneg_left _ hc
    apply add_le_add _ (mul_le_mul_of_nonneg_right hn hP)
    exact mul_le_mul hh (add_le_add le_rfl (mul_le_mul_of_nonneg_right hn hK))
      (add_nonneg (potential_nonneg _ _) (mul_nonneg (by positivity) hK)) (by positivity)
  rw [codeTree_cost]
  linarith [mul_le_mul_of_nonneg_right hn₀ hD]

variable [Fintype Ω]

theorem full_execution_entropy_overhead (p : Selection.Law Ω)
    (Q C₀ b c P D : ℝ) (hQ : 0<Q) (hC : 1≤C₀) (hb : 0≤b)
    (hc : 0≤c) (hP : 0≤P) (hD : 0≤D)
    (N H n : ℕ) (R : A→B→Prop)
    (allowed : Domains A B→Finset C) (read : CapReader A B C)
    (choose : Ω→I→Domains A B→Option C) (t : Ω→BinaryTree I) (U : Domains A B)
    (targets : Ω→I→List (A×B)) (counts : Ω→I→ℕ)
    (hcounts : ∀ ω i,counts ω i≤n)
    (hN : ∀ ω,(t ω).numNodes≤N) (hH : ∀ ω,(t ω).height≤H)
    (hallowed : ∀ ω i U x,choose ω i U=some x→x∈allowed U)
    (hvalid : ∀ ω i U x,choose ω i U=some x→
      ∃ S : Finset A,∃ T : Finset B,S.Nonempty ∧ T.Nonempty ∧
      (9/10:ℝ)*S.card≤(S∩U.1).card ∧ (9/10:ℝ)*T.card≤(T∩U.2).card ∧
      Q*exp (-b)≤(S.card:ℝ)*T.card ∧
      ((read U x).1.card:ℝ)≤C₀*Q/T.card ∧ ((read U x).2.card:ℝ)≤C₀*Q/S.card)
    (hcost : ∀ ω i U x,choose ω i U=some x→log (allowed U).card≤D+c*(potential Q U+P)) :
    let M := fun ω=>codeTree (countReader read)
      (countChoose R read (choose ω) (targets ω) (counts ω)) (t ω) U
    let S := univ.image M
    let msg : Ω→S := fun ω=>⟨M ω,mem_image.mpr ⟨ω,mem_univ _,rfl⟩⟩
    Selection.entropy (p.map msg)≤((2*N+1:ℕ):ℝ)*log 2+(N:ℝ)*(D+log (n+1:ℕ))+
      c*((H:ℝ)*(potential Q U+(N:ℝ)*(b+log 4+2*log C₀))+(N:ℝ)*P) := by
  have hn : 0≤log (n+1:ℕ) := log_nonneg (by exact_mod_cast Nat.le_add_left 1 n)
  have hV (ω : Ω) : ∀ i U x,countChoose R read (choose ω) (targets ω) (counts ω) i U=some x→
      ∃ S : Finset A,∃ T : Finset B,S.Nonempty ∧ T.Nonempty ∧
      (9/10:ℝ)*S.card≤(S∩U.1).card ∧ (9/10:ℝ)*T.card≤(T∩U.2).card ∧
      Q*exp (-b)≤(S.card:ℝ)*T.card ∧
      (((countReader read) U x).1.card:ℝ)≤C₀*Q/T.card ∧
      (((countReader read) U x).2.card:ℝ)≤C₀*Q/S.card := by
    intro i V x hx
    obtain ⟨y,hy,rfl⟩:=Option.map_eq_some_iff.mp hx
    exact hvalid ω i V y hy
  have hC' (ω : Ω) : ∀ i U x,countChoose R read (choose ω) (targets ω) (counts ω) i U=some x→
      log (countAlphabet allowed n U).card≤D+log (n+1:ℕ)+c*(potential Q U+P) := by
    intro i V x hx
    obtain ⟨y,hy,rfl⟩:=Option.map_eq_some_iff.mp hx
    rw [countAlphabet_log allowed n V ⟨y,hallowed ω i V y hy⟩]
    linarith [hcost ω i V y hy]
  dsimp only
  rw [add_assoc]
  apply tree_message_entropy _ (countAlphabet allowed n) (countReader read) U
    Subtype.val Subtype.val_injective N
  · intro g
    obtain ⟨ω,hω,he⟩:=mem_image.mp g.property
    rw [←he]
    exact (codeTree_numNodes _ _ _ _).trans (hN ω)
  · intro g
    obtain ⟨ω,hω,he⟩:=mem_image.mp g.property
    rw [←he]
    exact codeTree_mem _ _ _
      (countChoose_mem R read (choose ω) (targets ω) (counts ω) allowed n
        (hcounts ω) (hallowed ω)) (t ω) U
  · intro g
    obtain ⟨ω,hω,he⟩:=mem_image.mp g.property
    rw [←he]
    exact codeTree_cost_overhead Q C₀ b c P (D+log (n+1:ℕ)) hQ hC hb hc hP
      (add_nonneg hD hn) N H _ _ _ (hV ω) (hC' ω) (t ω) (hN ω) (hH ω) U

end
end SharpLogRamsey.ExecutedPotential

end

end OAI
