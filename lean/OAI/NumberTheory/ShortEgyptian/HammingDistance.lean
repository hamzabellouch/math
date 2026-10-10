import OAI.NumberTheory.ShortEgyptian.PrimeProducts

namespace OAI

universe uJ uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def hammingDistance {J : Type uJ} [Fintype J] (I K : J → Bool) : ℕ :=
  (univ.filter (fun j => I j ≠ K j)).card

lemma hamming_weight {J : Type uJ} [Fintype J] (I K : J → Bool) :
    (1/2:ℝ)^hammingDistance I K = ∏ j, if I j = K j then (1:ℝ) else 1/2 := by
  rw [prod_ite]
  simp only [prod_const_one,one_mul,prod_const,hammingDistance]

lemma hamming_moment {J : Type uJ} [Fintype J] (I : J → Bool) :
    (𝔼 K : J → Bool, (1/2:ℝ)^hammingDistance I K) = (3/4:ℝ)^Fintype.card J := by
  simp_rw [hamming_weight]
  rw [expect_prod_pi (fun j x => if I j = x then (1:ℝ) else 1/2)]
  have hh (j : J) : (𝔼 x : Bool, if I j = x then (1:ℝ) else 1/2) = 3/4 := by
    cases I j <;> norm_num [Finset.expect_eq_sum_div_card]
  simp only [hh,prod_const,card_univ]

lemma hamming_tail {J : Type uJ} [Fintype J] (I : J → Bool) (k : ℕ) :
    (𝔼 K : J → Bool, if hammingDistance I K < k then (1:ℝ) else 0) ≤
      (2:ℝ)^k*(3/4:ℝ)^Fintype.card J := by
  have hpoint (K : J → Bool) : (if hammingDistance I K < k then (1:ℝ) else 0) ≤
      (2:ℝ)^k*(1/2:ℝ)^hammingDistance I K := by
    split_ifs with h
    · have hp : (1/2:ℝ)^k ≤ (1/2:ℝ)^hammingDistance I K :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) h.le
      have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (2:ℝ)^k)
      have heq : (2:ℝ)^k*(1/2:ℝ)^k = 1 := by rw [← mul_pow]; norm_num
      rwa [heq] at hh
    · positivity
  calc
    _ ≤ 𝔼 K : J → Bool, (2:ℝ)^k*(1/2:ℝ)^hammingDistance I K := expect_le_expect (fun K _ => hpoint K)
    _ = _ := by rw [← mul_expect,hamming_moment]

lemma hamming_tail_exp {J : Type uJ} [Fintype J] (I : J → Bool) (k : ℕ)
    (hk : 4*k ≤ Fintype.card J) :
    (𝔼 K : J → Bool, if hammingDistance I K < k then (1:ℝ) else 0) ≤
      Real.exp (-(Fintype.card J:ℝ)/16) := by
  apply (hamming_tail I k).trans
  have hL : Real.log (3/4:ℝ) ≤ -(1/4:ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3/4)
    linarith
  have h2 : Real.log (2:ℝ) ≤ 3/4 := by linarith [Real.log_two_lt_d9]
  have hkR : 4*(k:ℝ) ≤ Fintype.card J := by exact_mod_cast hk
  rw [← Real.exp_log (by positivity : (0:ℝ)<(2:ℝ)^k*(3/4:ℝ)^Fintype.card J)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
  have h1 := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg (Fintype.card J))
  have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)
  nlinarith only [h1,h3,hkR]

lemma complex_expect_re {A : Type uA} [Fintype A] (f : A → ℂ) :
    (𝔼 a, f a).re = 𝔼 a, (f a).re := by
  simp only [Fintype.expect_eq_sum_div_card,Complex.div_re,Complex.re_sum,Complex.natCast_re,
    Complex.natCast_im,mul_zero,sum_div,Complex.normSq_natCast]
  by_cases hc : Fintype.card A = 0
  · simp [hc]
  · have hcR : (Fintype.card A:ℝ) ≠ 0 := by exact_mod_cast hc
    apply sum_congr rfl
    intro a _
    field_simp
    ring

lemma complex_expect_norm_sq {A : Type uA} [Fintype A] (f : A → ℂ) :
    ‖𝔼 a, f a‖^2 = 𝔼 a, 𝔼 b, (f a*(starRingEnd ℂ) (f b)).re := by
  have hh : ‖∑ a, f a‖^2 = ∑ a, ∑ b, (f a*(starRingEnd ℂ) (f b)).re := by
    rw [← Complex.normSq_eq_norm_sq,← Complex.ofReal_re (Complex.normSq _),← Complex.mul_conj]
    simp only [map_sum,sum_mul,mul_sum,Complex.re_sum]
    exact sum_comm
  simp only [Fintype.expect_eq_sum_div_card,norm_div,Complex.norm_natCast,div_pow,hh,← sum_div]
  ring

lemma mean_square_correlation_bound {A : Type uA} {J : Type uJ} [Fintype A] [Nonempty A] [Fintype J]
    (F : (J → Bool) → A → ℂ) (hnorm : ∀ I a, ‖F I a‖ ≤ 1)
    (k : ℕ) (epsilon : ℝ) (heps : 0 ≤ epsilon)
    (hcorr : ∀ I K, k ≤ hammingDistance I K →
      ‖𝔼 a, F I a*(starRingEnd ℂ) (F K a)‖ ≤ epsilon) :
    (𝔼 a, ‖𝔼 I : J → Bool, F I a‖^2) ≤
      (2:ℝ)^k*(3/4:ℝ)^Fintype.card J+epsilon := by
  have hpoint I K : (𝔼 a, (F I a*(starRingEnd ℂ) (F K a)).re) ≤
      (if hammingDistance I K < k then (1:ℝ) else 0)+epsilon := by
    rw [← complex_expect_re]
    apply (Complex.re_le_norm _).trans
    by_cases h : hammingDistance I K < k
    · rw [ite_eq_left h]
      apply ((RCLike.norm_expect_le (K := ℂ)).trans (expect_le univ_nonempty (fun a _ => ?_))).trans (by linarith : (1:ℝ)≤1+epsilon)
      rw [norm_mul,Complex.norm_conj]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hnorm I a)).trans (hnorm K a)
    · rw [ite_eq_right h,zero_add]
      exact hcorr I K (Nat.le_of_not_gt h)
  simp_rw [complex_expect_norm_sq]
  rw [expect_comm]
  calc
    _ = 𝔼 I : J → Bool, 𝔼 K : J → Bool, 𝔼 a, (F I a*(starRingEnd ℂ) (F K a)).re := by
      apply expect_congr rfl
      intro I _
      exact expect_comm _ _ _
    _ ≤ 𝔼 I : J → Bool, 𝔼 K : J → Bool,
      ((if hammingDistance I K < k then (1:ℝ) else 0)+epsilon) :=
      expect_le_expect (fun I _ => expect_le_expect (fun K _ => hpoint I K))
    _ ≤ _ := by
      apply expect_le univ_nonempty
      intro I _
      rw [expect_add_distrib,Fintype.expect_const]
      linarith [hamming_tail I k]

end ShortEgyptian

end OAI
