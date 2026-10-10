import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeConvolution
import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeMass

namespace OAI

/-! The small- and large-prime deletion in the double-convolution argument.
All errors are uniform over one-bounded coefficients. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszPrimeTerm (f : ℕ → ℂ) (N p : ℕ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) * f p * (∑ m ∈ Icc 1 (N / p), f m)

noncomputable def halaszPrimePrefix (f : ℕ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ p ∈ sievePrimesUpTo x, halaszPrimeTerm f N p

noncomputable def halaszPrimeBandConvolution (f : ℕ → ℂ) (N : ℕ) (L U : ℝ) : ℂ :=
  ∑ p ∈ mrtPrimeBand L U, halaszPrimeTerm f N p

lemma halasz_prime_term_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N p : ℕ) (hp : p.Prime) :
    ‖halaszPrimeTerm f N p‖ ≤ (N : ℝ) * (Real.log (p : ℝ) / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hdiv : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
    apply (le_div_iff₀ hp0).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  unfold halaszPrimeTerm
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  calc
    _ ≤ Real.log (p : ℝ) * 1 * ((N / p : ℕ) : ℝ) := by
      gcongr
      · exact hf p hp.pos
      · exact halasz_bounded_prefix_norm f hf (N / p)
    _ ≤ Real.log (p : ℝ) * ((N : ℝ) / p) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiv hlog
    _ = _ := by ring

lemma halasz_prime_set_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ‖∑ p ∈ P, halaszPrimeTerm f N p‖ ≤
      (N : ℝ) * ∑ p ∈ P, Real.log (p : ℝ) / p := by
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  exact sum_le_sum (fun p hp => halasz_prime_term_bound f hf N p (hP p hp))

lemma halasz_prime_prefix_eq (f : ℕ → ℂ) (N : ℕ) :
    halaszPrimePrefix f N N = halaszPrimeConvolution f N := by
  have he : sievePrimesUpTo (N : ℝ) = (Icc 1 N).filter Nat.Prime := by
    ext p
    simp only [sievePrimesUpTo, Nat.floor_natCast, mem_filter, mem_Iic, mem_Icc]
    exact ⟨fun h => ⟨⟨h.2.pos, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  simp only [halaszPrimePrefix, he, halaszPrimeConvolution, halaszPrimeTerm]

lemma halasz_prime_band_eq (f : ℕ → ℂ) (N : ℕ) {L U : ℝ} (hLU : L ≤ U) :
    halaszPrimeBandConvolution f N L U =
      halaszPrimePrefix f N U - halaszPrimePrefix f N L := by
  exact sum_sdiff_eq_sub (f := halaszPrimeTerm f N) (mrt_sievePrimesUpTo_mono hLU)

lemma halasz_prime_prefix_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ‖halaszPrimePrefix f N x‖ ≤ (N : ℝ) * (Real.log x + halaszMertensConstant) := by
  exact (halasz_prime_set_bound f hf N _ (sievePrimesUpTo_prime x)).trans
    (mul_le_mul_of_nonneg_left (halasz_prime_prefix_mass_le hx) (Nat.cast_nonneg _))

lemma halasz_prime_band_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) {L U : ℝ} (hL : 1 ≤ L) (hLU : L ≤ U) :
    ‖halaszPrimeBandConvolution f N L U‖ ≤
      (N : ℝ) * (Real.log U - Real.log L + 2 * halaszMertensConstant) := by
  exact (halasz_prime_set_bound f hf N _ (fun _ hp => mrtPrimeBand_prime hp)).trans
    (mul_le_mul_of_nonneg_left (halasz_prime_band_mass_le hL hLU) (Nat.cast_nonneg _))

/-- Delete all primes at most L and greater than N/2. -/
theorem halasz_prime_truncation_error (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) (hLN : L ≤ (N : ℝ) / 2) :
    ‖halaszPrimeConvolution f N - halaszPrimeBandConvolution f N L ((N : ℝ) / 2)‖ ≤
      (N : ℝ) * (Real.log L + Real.log 2 + 3 * halaszMertensConstant) := by
  have hN : (2 : ℝ) ≤ N := by linarith
  have hhalf : (N : ℝ) / 2 ≤ N := by linarith
  have he : halaszPrimeConvolution f N -
      halaszPrimeBandConvolution f N L ((N : ℝ) / 2) =
      halaszPrimePrefix f N L +
        halaszPrimeBandConvolution f N ((N : ℝ) / 2) N := by
    rw [halasz_prime_band_eq f N hLN, halasz_prime_band_eq f N hhalf,
      halasz_prime_prefix_eq]
    ring
  rw [he]
  calc
    _ ≤ ‖halaszPrimePrefix f N L‖ +
        ‖halaszPrimeBandConvolution f N ((N : ℝ) / 2) N‖ := norm_add_le _ _
    _ ≤ (N : ℝ) * (Real.log L + halaszMertensConstant) +
        (N : ℝ) * (Real.log 2 + 2 * halaszMertensConstant) := by
      apply add_le_add (halasz_prime_prefix_bound f hf N hL)
      exact (halasz_prime_set_bound f hf N _ (fun _ hp => mrtPrimeBand_prime hp)).trans
        (mul_le_mul_of_nonneg_left (halasz_upper_half_prime_mass hN) (Nat.cast_nonneg _))
    _ = _ := by ring

theorem halasz_truncated_convolution_mean_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) (hLN : L ≤ (N : ℝ) / 2) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖halaszPrimeBandConvolution f N L ((N : ℝ) / 2)‖ +
        (N : ℝ) * (Real.log L + Real.log 2 + 3 * halaszMertensConstant +
          halaszPrimePowerConstant + 1) := by
  have hN : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have ht := halasz_prime_truncation_error f hf N hL hLN
  have hm := halasz_prime_convolution_mean_bound f hf hmul N hN
  have hn := norm_add_le (halaszPrimeBandConvolution f N L ((N : ℝ) / 2))
    (halaszPrimeConvolution f N - halaszPrimeBandConvolution f N L ((N : ℝ) / 2))
  rw [add_sub_cancel] at hn
  linarith

end TwoPointCorrelations

end OAI
