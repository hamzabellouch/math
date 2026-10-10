import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.TreeDecoder
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalPotential
import OAI.Combinatorics.SharpRamsey.Trees.TreePotential

namespace OAI

section
namespace SharpLogRamsey.ExecutedPotential
open Finset Real BinaryTree TreeDecoder
open scoped Classical
noncomputable section
variable {A B I C : Type*}

def potential (Q : ℝ) (U : Domains A B) : ℝ :=
  max (log ((U.1.card:ℝ)*U.2.card/Q)) 0

lemma potential_nonneg (Q : ℝ) (U : Domains A B) : 0≤potential Q U := le_max_right _ _

lemma cap_potential_zero_allowed {b t Q C a' : ℝ} (hb : 0<b) (ht : 0<t)
    (hQ : 0<Q) (hC : 1≤C) (htb : t≤b) (ha' : 0≤a') (hcap : a'≤C*Q/t) :
    max (log (a'*b/Q)) 0≤log (b/t)+log C := by
  rcases ha'.eq_or_lt with hz | hp
  · rw [←hz]
    simp only [zero_mul,zero_div,log_zero,max_self]
    exact add_nonneg (ReciprocalPotential.gap_nonneg ht htb) (log_nonneg hC)
  · exact ReciprocalPotential.cap_potential hb ht hQ hC htb hp hcap

theorem branch (Q C b : ℝ) (hQ : 0<Q) (hC : 1≤C)
    (U V : Domains A B) (S : Finset A) (T : Finset B)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (htrimS : (9/10:ℝ)*S.card≤(S∩U.1).card)
    (htrimT : (9/10:ℝ)*T.card≤(T∩U.2).card)
    (hprod : Q*exp (-b)≤(S.card:ℝ)*T.card)
    (hcapA : (V.1.card:ℝ)≤C*Q/T.card)
    (hcapB : (V.2.card:ℝ)≤C*Q/S.card) :
    potential Q (V.1,U.2)+potential Q (U.1,V.2)≤
      potential Q U+(b+log 4+2*log C) := by
  have hs : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have ht : (0:ℝ)<T.card := by exact_mod_cast card_pos.mpr hT
  have hs' : (0:ℝ)<(S∩U.1).card := by linarith
  have ht' : (0:ℝ)<(T∩U.2).card := by linarith
  have hsu : ((S∩U.1).card:ℝ)≤U.1.card := by exact_mod_cast card_le_card inter_subset_right
  have htu : ((T∩U.2).card:ℝ)≤U.2.card := by exact_mod_cast card_le_card inter_subset_right
  have hsa : ((S∩U.1).card:ℝ)≤S.card := by exact_mod_cast card_le_card inter_subset_left
  have hta : ((T∩U.2).card:ℝ)≤T.card := by exact_mod_cast card_le_card inter_subset_left
  have hp' : Q*exp (-(b+log 4))≤((S∩U.1).card:ℝ)*(T∩U.2).card := by
    have he : exp (-(b+log 4))=exp (-b)/4 := by
      rw [neg_add,exp_add,exp_neg (log 4),exp_log (by norm_num : (0:ℝ)<4)]
      ring
    rw [he]
    have hh := mul_le_mul htrimS htrimT (by positivity) hs'.le
    nlinarith [mul_pos hs ht]
  have hca : (V.1.card:ℝ)≤C*Q/(T∩U.2).card :=
    hcapA.trans (div_le_div_of_nonneg_left (by positivity) ht' hta)
  have hcb : (V.2.card:ℝ)≤C*Q/(S∩U.1).card :=
    hcapB.trans (div_le_div_of_nonneg_left (by positivity) hs' hsa)
  have hl := cap_potential_zero_allowed (ht'.trans_le htu) ht' hQ hC htu
    (Nat.cast_nonneg V.1.card) hca
  have hr := cap_potential_zero_allowed (hs'.trans_le hsu) hs' hQ hC hsu
    (Nat.cast_nonneg V.2.card) hcb
  have hg := ReciprocalPotential.gap_sum (hs'.trans_le hsu) (ht'.trans_le htu) hs' ht' hQ hp'
  rw [mul_comm (V.2.card:ℝ) (U.1.card:ℝ)] at hr
  have hm : log ((U.1.card:ℝ)*U.2.card/Q)≤potential Q U := le_max_left _ _
  dsimp only [potential] at *
  linarith

def annotate (read : CapReader A B C) (choose : I→Domains A B→Option C) :
    BinaryTree I→Domains A B→BinaryTree (I×Domains A B×C)
  | .nil,_ => .nil
  | .node i l r,U => match choose i U with
    | none => .nil
    | some c =>
      let V := read U c
      .node (i,U,c) (annotate read choose l (V.1,U.2))
        (annotate read choose r (U.1,V.2))

lemma erase_annotate (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (t : BinaryTree I) (U : Domains A B) :
    (annotate read choose t U).map (fun z => (z.1,z.2.2))=execute read choose t U := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    cases hc : choose i U <;> simp only [annotate,execute,hc,BinaryTree.map,hl,hr]

lemma annotate_height (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (t : BinaryTree I) (U : Domains A B) :
    (annotate read choose t U).height≤t.height := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    simp only [annotate]
    split
    · simp
    · simp only [height]
      exact Nat.add_le_add_right (max_le_max (hl _) (hr _)) 1

lemma annotate_numNodes (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (t : BinaryTree I) (U : Domains A B) :
    (annotate read choose t U).numNodes≤t.numNodes := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    simp only [annotate]
    split
    · simp
    · simp only [numNodes]
      exact Nat.add_le_add_right (Nat.add_le_add (hl _) (hr _)) 1

lemma root_le (Q : ℝ) (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (t : BinaryTree I) (U : Domains A B) :
    TreePotential.root (fun z : I×Domains A B×C => potential Q z.2.1)
      (annotate read choose t U)≤potential Q U := by
  cases t with
  | nil => exact potential_nonneg Q U
  | node i l r =>
    simp only [annotate]
    split
    · exact potential_nonneg Q U
    · exact le_rfl

theorem admissible (Q C₀ b : ℝ) (hQ : 0<Q) (hC : 1≤C₀)
    (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (hvalid : ∀ i U c, choose i U=some c →
      ∃ S : Finset A, ∃ T : Finset B, S.Nonempty ∧ T.Nonempty ∧
      (9/10:ℝ)*S.card≤(S∩U.1).card ∧ (9/10:ℝ)*T.card≤(T∩U.2).card ∧
      Q*exp (-b)≤(S.card:ℝ)*T.card ∧
      ((read U c).1.card:ℝ)≤C₀*Q/T.card ∧ ((read U c).2.card:ℝ)≤C₀*Q/S.card)
    (t : BinaryTree I) (U : Domains A B) :
    TreePotential.Admissible (fun z : I×Domains A B×C => potential Q z.2.1)
      (b+log 4+2*log C₀) (annotate read choose t U) := by
  induction t generalizing U with
  | nil => trivial
  | node i l r hl hr =>
    simp only [annotate]
    split
    · trivial
    · rename_i c hc
      obtain ⟨S,T,hS,hT,htrS,htrT,hp,hca,hcb⟩ := hvalid i U c hc
      refine ⟨potential_nonneg Q U,?_,hl _,hr _⟩
      apply (add_le_add (root_le Q read choose l _) (root_le Q read choose r _)).trans
      exact branch Q C₀ b hQ hC U (read U c) S T hS hT htrS htrT hp hca hcb

end
end SharpLogRamsey.ExecutedPotential

end

end OAI
