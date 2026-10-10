import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedMessage

namespace OAI

section
namespace SharpLogRamsey.ExecutedPotential
open Finset Real BinaryTree TreeDecoder TreeCodeEntropy
open scoped Classical
noncomputable section
variable {A B C I Ω : Type*}

def countReader (read : CapReader A B C) : CapReader A B (C×ℕ) :=
  fun U x=>read U x.1

def countChoose (R : A→B→Prop) (read : CapReader A B C)
    (choose : I→Domains A B→Option C) (targets : I→List (A×B)) (counts : I→ℕ) :
    I→Domains A B→Option (C×ℕ) := fun i U=>
      (choose i U).map (fun c=>(c,(retained R (read U c) (targets i) (counts i)).length))

lemma fullMessage_eq_codeTree (R : A→B→Prop) (read : CapReader A B C)
    (choose : I→Domains A B→Option C) (targets : I→List (A×B)) (counts : I→ℕ)
    (t : BinaryTree I) (U : Domains A B) :
    message R read targets counts (execute read choose t U) U=
      codeTree (countReader read) (countChoose R read choose targets counts) t U := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    cases he : choose i U with
    | none => simp only [execute,he,message,codeTree,countChoose,Option.map_none,BinaryTree.map]
    | some c =>
      simp only [execute,he,message,codeTree,countChoose,Option.map_some,countReader,BinaryTree.map]
      exact congrArg₂ (fun x y=>BinaryTree.node _ x y) (hl _) (hr _)

def countAlphabet (allowed : Domains A B→Finset C) (n : ℕ) (U : Domains A B) : Finset (C×ℕ) :=
  allowed U ×ˢ range (n+1)

lemma countChoose_mem (R : A→B→Prop) (read : CapReader A B C)
    (choose : I→Domains A B→Option C) (targets : I→List (A×B)) (counts : I→ℕ)
    (allowed : Domains A B→Finset C) (n : ℕ)
    (hc : ∀ i,counts i≤n) (ha : ∀ i U c,choose i U=some c→c∈allowed U)
    (i : I) (U : Domains A B) (x : C×ℕ)
    (hx : countChoose R read choose targets counts i U=some x) : x∈countAlphabet allowed n U := by
  obtain ⟨c,he,rfl⟩:=Option.map_eq_some_iff.mp hx
  apply mem_product.mpr
  refine ⟨ha i U c he,mem_range.mpr ?_⟩
  have hh : (retained R (read U c) (targets i) (counts i)).length≤counts i :=
    List.length_take_le _ _
  have hn:=hc i
  omega

lemma countAlphabet_log (allowed : Domains A B→Finset C) (n : ℕ) (U : Domains A B) (h : (allowed U).Nonempty) :
    log (countAlphabet allowed n U).card=log (allowed U).card+log (n+1:ℕ) := by
  rw [countAlphabet,card_product,card_range,Nat.cast_mul]
  exact log_mul (by exact_mod_cast (card_pos.mpr h).ne') (by positivity)

variable [Fintype Ω]

theorem full_execution_entropy (p : Selection.Law Ω)
    (Q C₀ b c P : ℝ) (hQ : 0<Q) (hC : 1≤C₀) (hb : 0≤b) (hc : 0≤c) (hP : 0≤P)
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
    (hcost : ∀ ω i U x,choose ω i U=some x→log (allowed U).card≤c*(potential Q U+P)) :
    let M := fun ω=>codeTree (countReader read)
      (countChoose R read (choose ω) (targets ω) (counts ω)) (t ω) U
    let S := univ.image M
    let msg : Ω→S := fun ω=>⟨M ω,mem_image.mpr ⟨ω,mem_univ _,rfl⟩⟩
    Selection.entropy (p.map msg)≤((2*N+1:ℕ):ℝ)*log 2+
      (c+1)*((H:ℝ)*(potential Q U+(N:ℝ)*(b+log 4+2*log C₀))+
        (N:ℝ)*(P+log (n+1:ℕ))) := by
  have hn : 0≤log (n+1:ℕ) := log_nonneg (by exact_mod_cast Nat.le_add_left 1 n)
  have hV : ∀ ω i V x,countChoose R read (choose ω) (targets ω) (counts ω) i V=some x→
      ∃ S : Finset A,∃ T : Finset B,S.Nonempty ∧ T.Nonempty ∧
      (9/10:ℝ)*S.card≤(S∩V.1).card ∧ (9/10:ℝ)*T.card≤(T∩V.2).card ∧
      Q*exp (-b)≤(S.card:ℝ)*T.card ∧
      (((countReader read) V x).1.card:ℝ)≤C₀*Q/T.card ∧
      (((countReader read) V x).2.card:ℝ)≤C₀*Q/S.card := by
    intro ω i V x hx
    obtain ⟨y,hy,rfl⟩:=Option.map_eq_some_iff.mp hx
    exact hvalid ω i V y hy
  have hC' : ∀ ω i V x,countChoose R read (choose ω) (targets ω) (counts ω) i V=some x→
      log (countAlphabet allowed n V).card≤(c+1)*(potential Q V+(P+log (n+1:ℕ))) := by
    intro ω i V x hx
    obtain ⟨y,hy,rfl⟩:=Option.map_eq_some_iff.mp hx
    rw [countAlphabet_log allowed n V ⟨y,hallowed ω i V y hy⟩]
    have hbnd:=hcost ω i V y hy
    have hp:=potential_nonneg Q V
    nlinarith [mul_nonneg hc hn]
  dsimp only
  apply tree_message_entropy _ (countAlphabet allowed n) (countReader read) U
    Subtype.val Subtype.val_injective N
  · intro g
    obtain ⟨ω,hω,he⟩:=mem_image.mp g.property
    rw [←he]
    exact (codeTree_numNodes (countReader read)
      (countChoose R read (choose ω) (targets ω) (counts ω)) (t ω) U).trans (hN ω)
  · intro g
    obtain ⟨ω,hω,he⟩:=mem_image.mp g.property
    rw [←he]
    exact codeTree_mem (countAlphabet allowed n) (countReader read)
      (countChoose R read (choose ω) (targets ω) (counts ω))
      (countChoose_mem R read (choose ω) (targets ω) (counts ω) allowed n
        (hcounts ω) (hallowed ω)) (t ω) U
  · intro g
    obtain ⟨ω,hω,he⟩:=mem_image.mp g.property
    rw [←he]
    exact codeTree_cost_bound Q C₀ b (c+1) (P+log (n+1:ℕ)) hQ hC hb
      (by linarith) (add_nonneg hP hn) N H (countAlphabet allowed n) (countReader read)
      (countChoose R read (choose ω) (targets ω) (counts ω)) (hV ω) (hC' ω)
      (t ω) (hN ω) (hH ω) U

end
end SharpLogRamsey.ExecutedPotential

end

end OAI
