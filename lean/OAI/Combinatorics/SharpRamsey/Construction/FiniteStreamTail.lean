import Mathlib

namespace OAI

section
namespace SharpLogRamsey.FiniteStreamTail
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {α : Type*} [Fintype α]

def hits {N : ℕ} (S : Finset α) (z : Fin N→α) : ℕ :=
  (univ.filter (fun i=>z i∈S)).card

def probability (S : Finset α) : ℝ := (S.card:ℝ)/(Fintype.card α:ℝ)

lemma moment (S : Finset α) (N : ℕ) :
    (∑ z : Fin N→α,(2:ℝ)^hits S z)=
      ((Fintype.card α:ℝ)+(S.card:ℝ))^N := by
  have hp (z : Fin N→α) :
      (2:ℝ)^hits S z=∏ i,if z i∈S then (2:ℝ) else 1 := by
    simp only [prod_ite,hits,prod_const,one_pow,mul_one]
  have hs : (∑ a : α,if a∈S then (2:ℝ) else 1)=(Fintype.card α:ℝ)+(S.card:ℝ) := by
    have he (a : α) : (if a∈S then (2:ℝ) else 1)=1+(if a∈S then 1 else 0) := by
      split_ifs <;> norm_num
    simp only [he,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one,
      Fintype.sum_ite_mem,sum_const]
  simp_rw [hp]
  rw [←Fintype.prod_sum (fun (_ : Fin N) (a : α)=>if a∈S then (2:ℝ) else 1)]
  simp only [hs,prod_const,card_univ,Fintype.card_fin]

variable [Nonempty α]

lemma card_pos : (0:ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos

lemma average_moment (S : Finset α) (N : ℕ) :
    (∑ z : Fin N→α,(2:ℝ)^hits S z)/(Fintype.card (Fin N→α):ℝ) =
      (1+probability S)^N := by
  rw [moment]
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,←div_pow,probability]
  congr 1
  rw [add_div,div_self (ne_of_gt (card_pos (α:=α)))]

lemma average_moment_le (S : Finset α) (N : ℕ) :
    (∑ z : Fin N→α,(2:ℝ)^hits S z)/(Fintype.card (Fin N→α):ℝ) ≤
      exp (N*probability S) := by
  rw [average_moment,exp_nat_mul]
  apply pow_le_pow_left₀
  · exact add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · simpa only [add_comm] using Real.add_one_le_exp (probability S)

lemma single_tail (S : Finset α) (N : ℕ) (t : ℝ) :
    probability (univ.filter (fun z : Fin N→α=>t≤hits S z)) ≤
      exp (N*probability S-t*log 2) := by
  let B := univ.filter (fun z : Fin N→α=>t≤hits S z)
  have hsum : (B.card:ℝ)*exp (t*log 2)≤∑ z : Fin N→α,(2:ℝ)^hits S z := by
    calc
      _ = ∑ _z∈B,exp (t*log 2) := by simp
      _ ≤ ∑ z∈B,(2:ℝ)^hits S z := by
        apply sum_le_sum
        intro z hz
        have ht := (mem_filter.mp hz).2
        have he : exp ((hits S z:ℝ)*log 2)=(2:ℝ)^hits S z := by
          rw [exp_nat_mul,exp_log (by norm_num)]
        rw [←he]
        apply exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right ht (log_nonneg (by norm_num))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>by positivity)
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (Fintype.card (Fin N→α)))
  have hm := average_moment_le S N
  have hb : probability B*exp (t*log 2)≤exp (N*probability S) := by
    unfold probability
    calc
      _ = (B.card*exp (t*log 2))/(Fintype.card (Fin N→α):ℝ) := by ring
      _ ≤ _ := hdiv.trans hm
  have hh := (le_div_iff₀ (exp_pos (t*log 2))).mpr hb
  simpa only [exp_sub] using hh

lemma probability_univ : probability (univ : Finset α)=1 := by
  simp only [probability,card_univ]
  exact div_self (ne_of_gt (card_pos (α:=α)))

lemma probability_compl (S : Finset α) : probability Sᶜ=1-probability S := by
  simp only [probability,Finset.card_compl,Nat.cast_sub (card_le_univ S),sub_div,
    div_self (ne_of_gt (card_pos (α:=α)))]

omit [Nonempty α] [Fintype α] in
lemma hits_embedding {N n : ℕ} (S : Finset α) (z : Fin N→α) (e : Fin n↪Fin N) :
    hits S (z∘e)≤hits S z := by
  let A := univ.filter (fun i : Fin n=>z (e i)∈S)
  have he : A.map e⊆univ.filter (fun i : Fin N=>z i∈S) := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hi
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2⟩
  simpa only [card_map,A,hits,Function.comp_def] using card_le_card he

variable {J : Type*} [Fintype J]

theorem simultaneous_tail (R : J→Finset α) (N : ℕ) (t μ : ℝ)
    (hμ : ∀ j,(N:ℝ)*probability (R j)≤μ) :
    probability (univ.filter (fun z : Fin N→α=>∃ j,t≤hits (R j) z)) ≤
      (Fintype.card J:ℝ)*exp (μ-t*log 2) := by
  let B := fun j=>univ.filter (fun z : Fin N→α=>t≤hits (R j) z)
  have he : (univ.filter (fun z : Fin N→α=>∃ j,t≤hits (R j) z))=
      univ.biUnion B := by ext z; simp [B]
  rw [he]
  have hc : ((univ.biUnion B).card:ℝ)≤∑ j,((B j).card:ℝ) := by
    exact_mod_cast (card_biUnion_le (s:=univ) (t:=B))
  calc
    _ ≤ (∑ j,((B j).card:ℝ))/(Fintype.card (Fin N→α):ℝ) :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = ∑ j,probability (B j) := by rw [sum_div]; rfl
    _ ≤ ∑ _j : J,exp (μ-t*log 2) := by
      apply sum_le_sum
      intro j _
      exact (single_tail (R j) N t).trans (exp_le_exp.mpr (sub_le_sub_right (hμ j) _))
    _ = _ := by simp

end
end SharpLogRamsey.FiniteStreamTail

end

end OAI
