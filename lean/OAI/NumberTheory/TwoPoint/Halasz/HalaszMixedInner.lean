import OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedConvolution

namespace OAI

/-! The inner logarithmic approximation for the actual typical sequence.
The same estimate covers cofactors shorter than the deleted-prime cutoff. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_mixed_logarithmic_approximation_all (G B : ℕ → ℂ) (hB : OneBounded B)
    (N : ℕ) (_hN : 1 ≤ N) {L : ℝ} (hL : 1 ≤ L)
    (hmul : ∀ p : ℕ, p.Prime → L < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m) :
    ‖(∑ n ∈ Icc 1 N, B n*(Real.log (n:ℝ):ℂ)) -
      halaszMixedPrimeConvolution G B N L N‖ ≤
        (N:ℝ)*(halaszPrimePowerConstant+Real.log L+halaszMertensConstant) := by
  by_cases hLN : L ≤ (N:ℝ)
  · exact halasz_mixed_logarithmic_approximation G B hB N hL hLN hmul
  have hNL : (N:ℝ) < L := lt_of_not_ge hLN
  have hempty : mrtPrimeBand L N = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hb := mrtPrimeBand_bounds (by linarith : 0 ≤ L) (Nat.cast_nonneg N) hp
    linarith
  simp only [halaszMixedPrimeConvolution,hempty,sum_empty,sub_zero]
  have hc := halaszPrimePowerConstant_nonneg
  have hm := halaszMertensConstant_nonneg
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  calc
    _ ≤ ∑ n ∈ Icc 1 N, Real.log L := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro n hn
      have hn1 := (mem_Icc.mp hn).1
      have hln : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hln]
      apply (mul_le_of_le_one_left hln (hB n hn1)).trans
      apply Real.log_le_log (by exact_mod_cast hn1)
      exact (show (n:ℝ) ≤ N by exact_mod_cast (mem_Icc.mp hn).2).trans hNL.le
    _ = (N:ℝ)*Real.log L := by simp
    _ ≤ _ := by nlinarith [Nat.cast_nonneg (α:=ℝ) N]

lemma halasz_mixed_prefix_log (G B : ℕ → ℂ) (hB : OneBounded B)
    (N : ℕ) (hN : 1 ≤ N) {L : ℝ} (hL : 1 ≤ L)
    (hmul : ∀ p : ℕ, p.Prime → L < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m) :
    ‖(∑ n ∈ Icc 1 N, B n)*(Real.log (N:ℝ):ℂ) -
      halaszMixedPrimeConvolution G B N L N‖ ≤
        (halaszPrimePowerConstant+Real.log L+halaszMertensConstant+1)*(N:ℝ) := by
  have he := halasz_logarithmic_sum_error B hB N hN
  have hp := halasz_mixed_logarithmic_approximation_all G B hB N hN hL hmul
  have ht := norm_add_le
    ((∑ n ∈ Icc 1 N, B n)*(Real.log (N:ℝ):ℂ) -
      ∑ n ∈ Icc 1 N, B n*(Real.log (n:ℝ):ℂ))
    ((∑ n ∈ Icc 1 N, B n*(Real.log (n:ℝ):ℂ)) -
      halaszMixedPrimeConvolution G B N L N)
  rw [sub_add_sub_cancel] at ht
  nlinarith

lemma halasz_mixed_real_log_approximation (G B : ℕ → ℂ) (hB : OneBounded B)
    (N : ℕ) (hN : 1 ≤ N) {L : ℝ} (hL : 1 ≤ L)
    (hmul : ∀ p : ℕ, p.Prime → L < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m)
    {x : ℝ} (hNx : (N:ℝ) ≤ x) (hxN : x ≤ 2*N) :
    ‖(∑ n ∈ Icc 1 N, B n)*(Real.log x:ℂ) -
      halaszMixedPrimeConvolution G B N L N‖ ≤
        (halaszPrimePowerConstant+Real.log L+halaszMertensConstant+1+Real.log 2)*x := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hx0 : 0 < x := hN0.trans_le hNx
  have hgap0 : 0 ≤ Real.log x-Real.log (N:ℝ) :=
    sub_nonneg.mpr (Real.log_le_log hN0 hNx)
  have hgap2 : Real.log x-Real.log (N:ℝ) ≤ Real.log 2 := by
    have hh := Real.log_le_log hx0 hxN
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hN0.ne'] at hh
    linarith
  have he : (∑ n ∈ Icc 1 N, B n)*(Real.log x:ℂ) -
      halaszMixedPrimeConvolution G B N L N =
      (∑ n ∈ Icc 1 N, B n)*((Real.log x-Real.log (N:ℝ):ℝ):ℂ) +
      ((∑ n ∈ Icc 1 N, B n)*(Real.log (N:ℝ):ℂ) -
        halaszMixedPrimeConvolution G B N L N) := by push_cast; ring
  have hC : 0 ≤ halaszPrimePowerConstant+Real.log L+halaszMertensConstant+1+Real.log 2 := by
    have := halaszPrimePowerConstant_nonneg
    have := halaszMertensConstant_nonneg
    have := Real.log_nonneg hL
    positivity
  rw [he]
  calc
    _ ≤ ‖(∑ n ∈ Icc 1 N, B n)*((Real.log x-Real.log (N:ℝ):ℝ):ℂ)‖ +
        ‖(∑ n ∈ Icc 1 N, B n)*(Real.log (N:ℝ):ℂ) -
          halaszMixedPrimeConvolution G B N L N‖ := norm_add_le _ _
    _ ≤ (N:ℝ)*Real.log 2 +
        (halaszPrimePowerConstant+Real.log L+halaszMertensConstant+1)*(N:ℝ) := by
      apply add_le_add _ (halasz_mixed_prefix_log G B hB N hN hL hmul)
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hgap0]
      exact mul_le_mul (halasz_bounded_prefix_norm B hB N) hgap2 hgap0 (Nat.cast_nonneg N)
    _ = (halaszPrimePowerConstant+Real.log L+halaszMertensConstant+1+Real.log 2)*(N:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hNx hC

lemma halasz_mixed_real_inner_approximation (G B : ℕ → ℂ) (hB : OneBounded B)
    (N : ℕ) (hN : 1 ≤ N) {L : ℝ} (hL : 1 ≤ L)
    (hmul : ∀ p : ℕ, p.Prime → L < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m)
    {x : ℝ} (hx : 1 < x) (hNx : (N:ℝ) ≤ x) (hxN : x ≤ 2*N) :
    ‖(∑ n ∈ Icc 1 N, B n) - halaszMixedPrimeConvolution G B N L N/(Real.log x:ℂ)‖ ≤
      (halaszPrimePowerConstant+Real.log L+halaszMertensConstant+1+Real.log 2)*x/Real.log x := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hlogC : (Real.log x:ℂ) ≠ 0 := by exact_mod_cast hlog.ne'
  have he : (∑ n ∈ Icc 1 N, B n) - halaszMixedPrimeConvolution G B N L N/(Real.log x:ℂ) =
      ((∑ n ∈ Icc 1 N, B n)*(Real.log x:ℂ) -
        halaszMixedPrimeConvolution G B N L N)/(Real.log x:ℂ) := by field_simp
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlog]
  exact div_le_div_of_nonneg_right
    (halasz_mixed_real_log_approximation G B hB N hN hL hmul hNx hxN) hlog.le

end TwoPointCorrelations

end OAI
