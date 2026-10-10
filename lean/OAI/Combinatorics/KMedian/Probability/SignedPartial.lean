import Mathlib
import OAI.Combinatorics.KMedian.Rounding.WeightedRounding
import OAI.Combinatorics.KMedian.Probability.SumLaws
import OAI.Combinatorics.KMedian.Probability.ProbabilitySupport

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding
open Finset MarginalRounding
variable {I : Type} [Fintype I] [DecidableEq I]

theorem signed_terminal (p u : I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hu : ∀ i, 0 < u i → u i ≤ 1)
    (hpair : ∀ i ∈ fractional p, ∀ j ∈ fractional p, i ≠ j → ¬0 < u i*u j) :
    ∃ (μ : FiniteLaw (I → Bool)) (Q : (I → Bool) → I → ℝ),
      (∀ ω, 0 < μ.weight ω →
        (∀ i, 0 ≤ Q ω i) ∧ (∀ i, Q ω i ≤ 1) ∧
        (fractional (Q ω)).card ≤ 1 ∧
        (∑ i, u i*Q ω i) ≤ (∑ i, u i*p i)+1) ∧
      (∀ i, μ.expect (fun ω => Q ω i)=p i) ∧
      (∀ i j, i ≠ j → μ.expect (fun ω => Q ω i*Q ω j)=p i*p j) := by
  classical
  let μ := FiniteLaw.bernoulli p hp0 hp1
  let bit : (I → Bool) → I → ℝ := fun ω i => if ω i=true then 1 else 0
  let Q : (I → Bool) → I → ℝ := fun ω i => if u i<0 then p i else bit ω i
  have hb0 : ∀ ω i, 0 ≤ bit ω i := by intro ω i; dsimp only [bit]; split_ifs <;> norm_num
  have hb1 : ∀ ω i, bit ω i ≤ 1 := by intro ω i; dsimp only [bit]; split_ifs <;> norm_num
  have hmean : ∀ i, μ.expect (fun ω => bit ω i)=p i :=
    FiniteLaw.bernoulli_marginal p hp0 hp1
  have hfixed : ∀ ω, 0 < μ.weight ω → ∀ i, i ∉ fractional p → bit ω i=p i := by
    intro ω hω i hi
    rcases nonfractional_integral hp0 hp1 hi with hi0 | hi1
    · have hh := μ.prob_zero_support (fun ω => ω i=true) ((hmean i).trans hi0) ω hω
      simp only [bit,ite_eq_right hh,hi0]
    · have hh := μ.prob_one_support (fun ω => ω i=true) ((hmean i).trans hi1) ω hω
      simp only [bit,ite_eq_left hh,hi1]
  let P := (fractional p).filter (fun i => 0 < u i)
  let N := (fractional p).filter (fun i => u i < 0)
  have hP : P.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hij
    exact hpair i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij
      (mul_pos (mem_filter.mp hi).2 (mem_filter.mp hj).2)
  have hN : N.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hij
    exact hpair i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij
      (mul_pos_of_neg_of_neg (mem_filter.mp hi).2 (mem_filter.mp hj).2)
  refine ⟨μ,Q,?_,?_,?_⟩
  · intro ω hω
    have hq0 : ∀ i, 0 ≤ Q ω i := by intro i; dsimp only [Q]; split_ifs; exact hp0 i; exact hb0 ω i
    have hq1 : ∀ i, Q ω i ≤ 1 := by intro i; dsimp only [Q]; split_ifs; exact hp1 i; exact hb1 ω i
    refine ⟨hq0,hq1,?_,?_⟩
    · apply le_trans (card_le_card (show fractional (Q ω) ⊆ N from ?_)) hN
      intro i hi
      have hneg : u i<0 := by
        by_contra hn
        have hh := (mem_fractional _ _).mp hi
        simp only [Q,ite_eq_right hn,bit] at hh
        split_ifs at hh <;> linarith only [hh.1,hh.2]
      exact mem_filter.mpr ⟨by simpa only [mem_fractional,Q,ite_eq_left hneg] using hi,hneg⟩
    · have hz : ∀ i, i ∉ P → u i*(Q ω i-p i)=0 := by
        intro i hi
        by_cases hn : u i<0
        · simp only [Q,ite_eq_left hn,sub_self,mul_zero]
        by_cases he : u i=0
        · rw [he,zero_mul]
        have hp : 0 < u i := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm he)
        have hnf : i ∉ fractional p := fun hf => hi (mem_filter.mpr ⟨hf,hp⟩)
        simp only [Q,ite_eq_right hn,hfixed ω hω i hnf,sub_self,mul_zero]
      have ht : ∀ i ∈ P, u i*(Q ω i-p i) ≤ 1 := by
        intro i hi
        have hui := (mem_filter.mp hi).2
        calc
          _ ≤ u i*1 := mul_le_mul_of_nonneg_left (by linarith only [hq1 i,hp0 i]) hui.le
          _ ≤ 1 := by simpa only [mul_one] using hu i hui
      have hsum : (∑ i, u i*(Q ω i-p i)) ≤ 1 := by
        rw [← sum_subset (subset_univ P) (fun i _ hi => hz i hi)]
        calc
          _ ≤ ∑ _i ∈ P, (1:ℝ) := sum_le_sum ht
          _ = (P.card:ℝ) := by simp only [sum_const,nsmul_eq_mul,mul_one]
          _ ≤ 1 := by exact_mod_cast hP
      simp only [mul_sub,sum_sub_distrib] at hsum
      linarith only [hsum]
  · intro i
    dsimp only [Q]
    by_cases hn : u i<0
    · simp only [hn,ite_true,FiniteLaw.expect_const]
    · simp only [ite_eq_right hn,hmean]
  · intro i j hij
    by_cases hi : u i<0 <;> by_cases hj : u j<0
    · simp only [Q,ite_eq_left hi,ite_eq_left hj,FiniteLaw.expect_const]
    · simp only [Q,ite_eq_left hi,ite_eq_right hj,FiniteLaw.expect_mul,hmean]
    · simp only [Q,ite_eq_right hi,ite_eq_left hj,FiniteLaw.expect_mul_right,hmean]
    · simp only [Q,ite_eq_right hi,ite_eq_right hj]
      have he : ∀ ω, bit ω i*bit ω j=if ω i=true ∧ ω j=true then (1:ℝ) else 0 := by
        intro ω; dsimp only [bit]; split_ifs <;> simp_all
      simp_rw [he]
      exact FiniteLaw.bernoulli_pair p hp0 hp1 hij

theorem exists_signed_partial_law (p u : I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hu : ∀ i, 0 < u i → u i ≤ 1) :
    ∃ (Ω : Type) (inst : Fintype Ω), letI := inst;
      ∃ (μ : FiniteLaw Ω) (Q : Ω → I → ℝ),
        (∀ ω, 0 < μ.weight ω →
          (∀ i, 0 ≤ Q ω i) ∧ (∀ i, Q ω i ≤ 1) ∧
          (fractional (Q ω)).card ≤ 1 ∧
          (∑ i, u i*Q ω i) ≤ (∑ i, u i*p i)+1) ∧
        (∀ i, μ.expect (fun ω => Q ω i)=p i) ∧
        (∀ i j, i ≠ j → μ.expect (fun ω => Q ω i*Q ω j) ≤ p i*p j) := by
  classical
  suffices h : ∀ n : ℕ, ∀ p : I → ℝ, (fractional p).card=n →
      (∀ i, 0 ≤ p i) → (∀ i, p i ≤ 1) →
      ∃ (Ω : Type) (inst : Fintype Ω), letI := inst;
        ∃ (μ : FiniteLaw Ω) (Q : Ω → I → ℝ),
          (∀ ω, 0 < μ.weight ω →
            (∀ i, 0 ≤ Q ω i) ∧ (∀ i, Q ω i ≤ 1) ∧
            (fractional (Q ω)).card ≤ 1 ∧
            (∑ i, u i*Q ω i) ≤ (∑ i, u i*p i)+1) ∧
          (∀ i, μ.expect (fun ω => Q ω i)=p i) ∧
          (∀ i j, i ≠ j → μ.expect (fun ω => Q ω i*Q ω j) ≤ p i*p j) by
    exact h _ p rfl hp0 hp1
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hn hp0 hp1
    by_cases hpair : ∃ i ∈ fractional p, ∃ j ∈ fractional p, i ≠ j ∧ 0 < u i*u j
    · obtain ⟨i,hi,j,hj,hij,hsign⟩ := hpair
      let r := u i/u j
      have hr : 0 < r := by
        rcases mul_pos_iff.mp hsign with hh | hh
        · exact div_pos hh.1 hh.2
        · exact div_pos_of_neg_of_neg hh.1 hh.2
      let a := up p i j r
      let b := down p i j r
      have ha : 0 < a := up_pos hr hi hj
      have hb : 0 < b := down_pos hr hi hj
      have hqa := move_bounds hp0 hp1 hij hr (show -b ≤ a by linarith only [ha,hb]) (le_refl a)
      have hqb := move_bounds hp0 hp1 hij hr (le_refl (-b)) (show -b ≤ a by linarith only [ha,hb])
      obtain ⟨Ω,instΩ,hexμ⟩ := ih _ (hn ▸ up_smaller hr hij hi hj) (move p i j r a) rfl hqa.1 hqa.2
      let := instΩ
      obtain ⟨μ,Q,hsμ,hmμ,hpμ⟩ := hexμ
      obtain ⟨Ξ,instΞ,hexν⟩ := ih _ (hn ▸ down_smaller hr hij hi hj) (move p i j r (-b)) rfl hqb.1 hqb.2
      let := instΞ
      obtain ⟨ν,R,hsν,hmν,hpν⟩ := hexν
      let θ := b/(a+b)
      have hθ0 : 0 ≤ θ := (div_pos hb (add_pos ha hb)).le
      have hθ1 : θ ≤ 1 := (div_le_one (add_pos ha hb)).mpr (by linarith only [ha])
      have huj : u j ≠ 0 := by intro hh; rw [hh,mul_zero] at hsign; exact lt_irrefl _ hsign
      have hwa : (∑ k, u k*move p i j r a k)=∑ k, u k*p k := weighted_sum u p huj a
      have hwb : (∑ k, u k*move p i j r (-b) k)=∑ k, u k*p k := weighted_sum u p huj (-b)
      refine ⟨Ω ⊕ Ξ,inferInstance,FiniteLaw.sumMix θ hθ0 hθ1 μ ν,Sum.elim Q R,?_,?_,?_⟩
      · apply FiniteLaw.property_sumMix θ hθ0 hθ1 μ ν
        · intro ω hω
          simpa only [Sum.elim_inl,hwa] using hsμ ω hω
        · intro ξ hξ
          simpa only [Sum.elim_inr,hwb] using hsν ξ hξ
      · intro k
        rw [FiniteLaw.expect_sumMix]
        simp only [Sum.elim_inl,Sum.elim_inr,hmμ,hmν]
        exact endpoint_mean p i j k r ha hb
      · intro k l hkl
        rw [FiniteLaw.expect_sumMix]
        simp only [Sum.elim_inl,Sum.elim_inr]
        calc
          _ ≤ θ*(move p i j r a k*move p i j r a l)+
              (1-θ)*(move p i j r (-b) k*move p i j r (-b) l) :=
            add_le_add (mul_le_mul_of_nonneg_left (hpμ k l hkl) hθ0)
              (mul_le_mul_of_nonneg_left (hpν k l hkl) (sub_nonneg.mpr hθ1))
          _ ≤ p k*p l := endpoint_pair p i j hkl hr.le ha hb
    · obtain ⟨μ,Q,hs,hm,hp⟩ := signed_terminal p u hp0 hp1 hu (by
        intro i hi j hj hij hp
        exact hpair ⟨i,hi,j,hj,hij,hp⟩)
      exact ⟨I → Bool,inferInstance,μ,Q,hs,hm,fun i j hij => (hp i j hij).le⟩

end MetricKMedian.WeightedRounding
end
end

end OAI
