import OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedInner
import OAI.NumberTheory.TwoPoint.Halasz.HalaszDenominatorMass
import OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedBounds

namespace OAI

/-! Two logarithmic convolutions with a prime cutoff above every selected
typical band. No multiplicativity of the typical coefficient is asserted. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszMixedDouble (G B : ℕ → ℂ) (N : ℕ) (R : ℝ) : ℂ :=
  halaszMixedGrouped G B N R (mrtPrimeBand R ((N:ℝ)/2))

noncomputable def halaszMixedErrorConstant (R : ℝ) : ℝ :=
  halaszPrimePowerConstant+Real.log R+halaszMertensConstant+1+Real.log 2

lemma halasz_mixed_error_nonneg {R : ℝ} (hR : 1 ≤ R) :
    0 ≤ halaszMixedErrorConstant R := by
  have := halaszPrimePowerConstant_nonneg
  have := halaszMertensConstant_nonneg
  have := Real.log_nonneg hR
  unfold halaszMixedErrorConstant
  positivity

theorem halasz_mixed_double_error (G B : ℕ → ℂ) (hG : OneBounded G) (hB : OneBounded B)
    (N : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hmul : ∀ p : ℕ, p.Prime → R < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m) :
    ‖halaszMixedPrimeConvolution G B N R ((N:ℝ)/2)-halaszMixedDouble G B N R‖ ≤
      halaszMixedErrorConstant R*(N:ℝ)*∑ p ∈ mrtPrimeBand R ((N:ℝ)/2),
        Real.log (p:ℝ)/((p:ℝ)*Real.log ((N:ℝ)/p)) := by
  unfold halaszMixedPrimeConvolution halaszMixedDouble halaszMixedGrouped
  rw [← sum_sub_distrib,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  have hprime := mrtPrimeBand_prime hp
  have hb := mrtPrimeBand_bounds (by linarith : 0 ≤ R) (by positivity : (0:ℝ)≤(N:ℝ)/2) hp
  have hpN : 2*p ≤ N := by exact_mod_cast (show 2*(p:ℝ)≤N by linarith)
  obtain ⟨hM,hMx,hxM⟩ := halasz_divisor_cutoff hprime.pos hpN
  have hp0 : (0:ℝ)<p := by exact_mod_cast hprime.pos
  have hx : 1 < (N:ℝ)/p := by
    have hh : (2:ℝ)≤(N:ℝ)/p := (le_div_iff₀ hp0).mpr (by linarith)
    linarith
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
  rw [← mul_sub,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
  calc
    _ ≤ Real.log (p:ℝ)*1*(halaszMixedErrorConstant R*((N:ℝ)/p)/Real.log ((N:ℝ)/p)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hG p hprime.pos) hlog
      · exact halasz_mixed_real_inner_approximation G B hB (N/p) hM hR hmul hx hMx hxM
      · exact norm_nonneg _
      · positivity
    _ = _ := by ring

lemma halasz_mixed_upper_truncation (G B : ℕ → ℂ) (hG : OneBounded G)
    (hB : OneBounded B) (N : ℕ) {R : ℝ} (hR : 1 ≤ R) (hRN : R ≤ (N:ℝ)/2) :
    ‖halaszMixedPrimeConvolution G B N R N-
      halaszMixedPrimeConvolution G B N R ((N:ℝ)/2)‖ ≤
      (N:ℝ)*(Real.log 2+2*halaszMertensConstant) := by
  have hsub : mrtPrimeBand R ((N:ℝ)/2) ⊆ mrtPrimeBand R N := by
    apply sdiff_subset_sdiff_left
    exact mrt_sievePrimesUpTo_mono (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  have he : mrtPrimeBand R N \ mrtPrimeBand R ((N:ℝ)/2) = mrtPrimeBand ((N:ℝ)/2) N := by
    ext p
    simp only [mrtPrimeBand,mem_sdiff]
    have hRsub := mrt_sievePrimesUpTo_mono hRN
    tauto
  unfold halaszMixedPrimeConvolution
  rw [← sum_sdiff hsub,he,add_sub_cancel_right]
  calc
    _ ≤ (N:ℝ)*∑ p ∈ mrtPrimeBand ((N:ℝ)/2) N, Real.log (p:ℝ)/p := by
      rw [mul_sum]
      exact (norm_sum_le _ _).trans (sum_le_sum (fun p hp =>
        halasz_mixed_prime_term_bound G B hG hB N p (mrtPrimeBand_prime hp)))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (halasz_upper_half_prime_mass (by linarith : (2:ℝ)≤N)) (Nat.cast_nonneg N)

theorem halasz_mixed_double_mean (G B : ℕ → ℂ) (hG : OneBounded G) (hB : OneBounded B)
    (N : ℕ) {R : ℝ} (hR : 1 ≤ R) (hRN : R ≤ (N:ℝ)/2)
    (hmul : ∀ p : ℕ, p.Prime → R < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m) :
    Real.log (N:ℝ)*‖∑ n ∈ Icc 1 N, B n‖ ≤ ‖halaszMixedDouble G B N R‖ +
      (N:ℝ)*((halaszPrimePowerConstant+Real.log R+3*halaszMertensConstant+1+Real.log 2)+
        halaszMixedErrorConstant R*(Real.log (Real.log N)-Real.log (Real.log 2)+
          2*halaszMertensConstant/Real.log 2)) := by
  have hN : 1 ≤ N := by exact_mod_cast (show (1:ℝ)≤N by linarith)
  have hp := halasz_mixed_prefix_log G B hB N hN hR hmul
  have hu := halasz_mixed_upper_truncation G B hG hB N hR hRN
  have hd := halasz_mixed_double_error G B hG hB N hR hmul
  have hm := mul_le_mul_of_nonneg_left (halasz_denominator_prime_mass hR hRN)
    (mul_nonneg (halasz_mixed_error_nonneg hR) (Nat.cast_nonneg N))
  have hn := norm_add_le (halaszMixedDouble G B N R)
    (halaszMixedPrimeConvolution G B N R ((N:ℝ)/2)-halaszMixedDouble G B N R)
  rw [add_sub_cancel] at hn
  have ht := norm_add_le (halaszMixedPrimeConvolution G B N R ((N:ℝ)/2))
    (halaszMixedPrimeConvolution G B N R N-halaszMixedPrimeConvolution G B N R ((N:ℝ)/2))
  rw [add_sub_cancel] at ht
  have hs := norm_add_le (halaszMixedPrimeConvolution G B N R N)
    ((∑ n ∈ Icc 1 N, B n)*(Real.log (N:ℝ):ℂ)-halaszMixedPrimeConvolution G B N R N)
  rw [add_sub_cancel,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hN))] at hs
  nlinarith

end TwoPointCorrelations

end OAI
