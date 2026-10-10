import Mathlib

namespace OAI

namespace SharpRamseyFive.Metadata
open scoped BigOperators Classical

def TwoListCode (V : Type*) (h p B : ℕ) :=
  (Fin h→Fin 5→V) × (Fin p→Fin 5→V) × Fin (B+1) ×
    (Fin h→Fin (B+1)) × (Fin p→Fin (B+1)) × (Fin h×Fin p→Fin (B+1))

instance {V : Type*} [Fintype V] (h p B : ℕ) : Fintype (TwoListCode V h p B) :=
  inferInstanceAs (Fintype (_ × _ × _ × _ × _ × _))

lemma card_TwoListCode {V : Type*} [Fintype V] (h p B : ℕ) :
    Nat.card (TwoListCode V h p B)=Nat.card V^(5*(h+p))*(B+1)^(1+h+p+h*p) := by
  simp only [TwoListCode,Nat.card_prod,Nat.card_fun,Nat.card_fin]
  simp only [pow_mul,pow_add,pow_one]
  ring

def ListProfile (H J : ℕ) := {z : Fin (H+1)×Fin (H+1) // z.1.val*z.2.val≤J}

instance (H J : ℕ) : Fintype (ListProfile H J) :=
  inferInstanceAs (Fintype {profile : Fin (H+1)×Fin (H+1) // profile.1.val*profile.2.val≤J})

def TrainingCode (V : Type*) (H J B : ℕ) :=
  (r : ListProfile H J) × TwoListCode V r.val.1.val r.val.2.val B

instance {V : Type*} [Fintype V] (H J B : ℕ) : Fintype (TrainingCode V H J B) :=
  inferInstanceAs (Fintype ((r : ListProfile H J) × TwoListCode V r.val.1.val r.val.2.val B))

instance {V : Type*} [Nonempty V] (H J B : ℕ) : Nonempty (TrainingCode V H J B) := by
  classical
  refine ⟨⟨⟨(⟨0,by omega⟩,⟨0,by omega⟩),by simp⟩,?_,?_,?_,?_,?_,?_⟩⟩
  · exact fun _ _=>Classical.choice inferInstance
  · exact fun _ _=>Classical.choice inferInstance
  · exact ⟨0,by omega⟩
  · exact fun _=>⟨0,by omega⟩
  · exact fun _=>⟨0,by omega⟩
  · exact fun _=>⟨0,by omega⟩

lemma card_profile (H J : ℕ) : Nat.card (ListProfile H J)≤(H+1)^2 := by
  have h := Nat.card_le_card_of_injective (fun z : ListProfile H J=>z.val) Subtype.val_injective
  simpa only [ListProfile,Nat.card_prod,Nat.card_fin,pow_two] using h

theorem card_TrainingCode {V : Type*} [Fintype V] [Nonempty V] (H J B : ℕ) :
    Nat.card (TrainingCode V H J B)≤
      (H+1)^2*Nat.card V^(10*H)*(B+1)^(1+2*H+J) := by
  change Nat.card ((r : ListProfile H J) × TwoListCode V r.val.1.val r.val.2.val B)≤_
  rw [Nat.card_sigma]
  have hV : 1≤Nat.card V := Nat.card_pos
  calc
    _ ≤ ∑ _r : ListProfile H J,Nat.card V^(10*H)*(B+1)^(1+2*H+J) := by
      apply Finset.sum_le_sum
      intro r _
      rw [card_TwoListCode]
      have hh : r.val.1.val≤H := Nat.le_of_lt_succ r.val.1.isLt
      have hp : r.val.2.val≤H := Nat.le_of_lt_succ r.val.2.isLt
      exact Nat.mul_le_mul (Nat.pow_le_pow_right hV (by omega))
        (Nat.pow_le_pow_right (by omega : 1≤B+1) (by have := r.prop;omega))
    _ = Nat.card (ListProfile H J)*(Nat.card V^(10*H)*(B+1)^(1+2*H+J)) := by simp [Nat.card_eq_fintype_card]
    _ ≤ _ := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_right _ (card_profile H J)

theorem log_card_TrainingCode {V : Type*} [Fintype V] [Nonempty V] (H J B : ℕ) :
    Real.log (Nat.card (TrainingCode V H J B))≤
      2*Real.log (H+1)+(10*(H:ℝ))*Real.log (Nat.card V)+
        (1+2*(H:ℝ)+J)*Real.log (B+1) := by
  have hV : (0:ℝ)<Nat.card V := by exact_mod_cast Nat.card_pos (α:=V)
  have hh : (0:ℝ)<H+1 := by positivity
  have hb : (0:ℝ)<B+1 := by positivity
  have hc := Real.log_le_log (show (0:ℝ)<Nat.card (TrainingCode V H J B) by exact_mod_cast Nat.card_pos (α:=TrainingCode V H J B))
    (show (Nat.card (TrainingCode V H J B):ℝ)≤(H+1)^2*(Nat.card V:ℝ)^(10*H)*(B+1)^(1+2*H+J) by
      exact_mod_cast card_TrainingCode (V:=V) H J B)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_pow] at hc
  push_cast at hc
  exact hc

end SharpRamseyFive.Metadata

end OAI
