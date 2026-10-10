import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedFullMessage

namespace OAI

section
namespace SharpLogRamsey.ExecutedPotential
open Finset BinaryTree TreeDecoder Real
open scoped Classical
noncomputable section
variable {A B C I : Type*}

lemma flagDomain_size (R : A→B→Prop) (V : Domains A B)
    (S : Finset A) (T : Finset B) (hS : S.Nonempty) (hT : T.Nonempty)
    (Q C₀ b : ℝ) (hQ : 0<Q) (hC : 0≤C₀)
    (hprod : Q*exp (-b)≤(S.card:ℝ)*T.card)
    (hA : (V.1.card:ℝ)≤C₀*Q/T.card) (hB : (V.2.card:ℝ)≤C₀*Q/S.card) :
    ((flagDomain R V).card:ℝ)≤C₀^2*Q*exp b := by
  have hs : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have ht : (0:ℝ)<T.card := by exact_mod_cast card_pos.mpr hT
  have he : exp (-b)*exp b=1 := by rw [←exp_add]; simp only [neg_add_cancel,exp_zero]
  have hq : Q≤((S.card:ℝ)*T.card)*exp b := by
    have hh:=mul_le_mul_of_nonneg_right hprod (exp_nonneg b)
    simpa only [mul_assoc,he,mul_one] using hh
  have hd : Q/((S.card:ℝ)*T.card)≤exp b := (div_le_iff₀ (mul_pos hs ht)).mpr (by
    simpa only [mul_comm] using hq)
  have hm : (V.1.card:ℝ)*V.2.card≤(C₀*Q/T.card)*(C₀*Q/S.card) :=
    mul_le_mul hA hB (by positivity) (div_nonneg (mul_nonneg hC hQ.le) ht.le)
  have hid : (C₀*Q/T.card)*(C₀*Q/S.card)=C₀^2*Q*(Q/((S.card:ℝ)*T.card)) := by
    field_simp
  have hcard : (flagDomain R V).card≤V.1.card*V.2.card := by
    dsimp only [flagDomain]
    exact (card_filter_le _ _).trans_eq (card_product _ _)
  calc
    _ ≤ (V.1.card:ℝ)*V.2.card := by exact_mod_cast hcard
    _ ≤ C₀^2*Q*exp b := (hm.trans_eq hid).trans
      (mul_le_mul_of_nonneg_left hd (mul_nonneg (sq_nonneg C₀) hQ.le))

theorem decoded_domains_size (R : A→B→Prop) (read : CapReader A B C)
    (choose : I→Domains A B→Option C) (targets : I→List (A×B)) (counts : I→ℕ)
    (K : ℝ)
    (hcap : ∀ i U c,choose i U=some c→((flagDomain R (read U c)).card:ℝ)≤K)
    (t : BinaryTree I) (U : Domains A B) :
    ∀ D∈decode R read (message R read targets counts (execute read choose t U) U) U,
      (D.card:ℝ)≤K := by
  induction t generalizing U with
  | nil => simp only [execute,message,decode,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | node i l r hl hr =>
    cases he : choose i U with
    | none => simp only [execute,he,message,decode,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
    | some c =>
      simp only [execute,he,message,decode,List.mem_append]
      intro D hD
      rcases hD with (hD | hD) | hD
      · exact hl _ D hD
      · obtain ⟨_,rfl⟩:=List.mem_replicate.mp hD
        exact hcap i U c he
      · exact hr _ D hD

theorem reciprocal_decoded_domains_size (R : A→B→Prop) (read : CapReader A B C)
    (choose : I→Domains A B→Option C) (targets : I→List (A×B)) (counts : I→ℕ)
    (Q C₀ b : ℝ) (hQ : 0<Q) (hC : 0≤C₀)
    (hvalid : ∀ i U x,choose i U=some x→
      ∃ S : Finset A,∃ T : Finset B,S.Nonempty ∧ T.Nonempty ∧
      Q*exp (-b)≤(S.card:ℝ)*T.card ∧
      ((read U x).1.card:ℝ)≤C₀*Q/T.card ∧ ((read U x).2.card:ℝ)≤C₀*Q/S.card)
    (t : BinaryTree I) (U : Domains A B) :
    ∀ D∈decode R read (message R read targets counts (execute read choose t U) U) U,
      (D.card:ℝ)≤C₀^2*Q*exp b := by
  apply decoded_domains_size R read choose targets counts
  intro i V x hx
  obtain ⟨S,T,hS,hT,hprod,hA,hB⟩:=hvalid i V x hx
  exact flagDomain_size R (read V x) S T hS hT Q C₀ b hQ hC hprod hA hB

end
end SharpLogRamsey.ExecutedPotential

end

end OAI
