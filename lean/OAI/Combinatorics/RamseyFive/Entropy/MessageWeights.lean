import Mathlib

namespace OAI

namespace SharpRamseyFive.MessageWeights
open scoped BigOperators
universe u v

lemma log_card_weight (A : Type u) [Fintype A] :
    (∑_a : A,Real.exp (-Real.log (Fintype.card A:ℝ)))≤1 := by
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  by_cases h : Fintype.card A=0
  · simp [h]
  · have hp : (0:ℝ)<Fintype.card A := by exact_mod_cast Nat.pos_of_ne_zero h
    rw [Real.exp_neg,Real.exp_log hp]
    exact le_of_eq (mul_inv_cancel₀ hp.ne')

lemma sigma_weight_le (A : Type u) [Fintype A] (B : A→Type v) [∀a,Fintype (B a)]
    (c : A→ℝ) (d : ∀a,B a→ℝ)
    (hc : (∑a,Real.exp (-c a))≤1) (hd : ∀a,(∑b,Real.exp (-d a b))≤1) :
    (∑m : Sigma B,Real.exp (-(c m.1+d m.1 m.2)))≤1 := by
  rw [Fintype.sum_sigma]
  apply le_trans _ hc
  apply Finset.sum_le_sum
  intro a _
  simp only [neg_add,Real.exp_add,←Finset.mul_sum]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hd a) (Real.exp_pos (-c a)).le

lemma sigma_header_weight (A : Type u) [Fintype A] (B : A→Type v) [∀a,Fintype (B a)]
    (d : ∀a,B a→ℝ) (hd : ∀a,(∑b,Real.exp (-d a b))≤1) :
    (∑m : Sigma B,Real.exp (-(Real.log (Fintype.card A:ℝ)+d m.1 m.2)))≤1 :=
  sigma_weight_le A B _ d (log_card_weight A) hd
lemma sum_bit_weight (A : Type u) (B : Type v) [Fintype A] [Fintype B]
    (c : A→ℝ) (d : B→ℝ)
    (hc : (∑a,Real.exp (-c a))≤1) (hd : (∑b,Real.exp (-d b))≤1) :
    (∑m : A⊕B,Real.exp (-(Real.log 2+Sum.elim c d m)))≤1 := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,neg_add,Real.exp_add,←Finset.mul_sum,
    Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
  simp only [Real.exp_neg] at hc hd
  norm_num only [invOf_eq_inv, inv_mul_eq_div] at *
  linarith only [hc,hd]

end SharpRamseyFive.MessageWeights

end OAI
