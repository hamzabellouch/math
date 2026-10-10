import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeTruncation
import OAI.NumberTheory.TwoPoint.Halasz.HalaszInnerApproximation

namespace OAI

/-! Apply the prime convolution a second time, retaining the varying
denominator log(N/p). This is the adaptive triple sum in the short proof of
Halasz's theorem. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszDoubleConvolution (f : ℕ → ℂ) (N : ℕ) (L : ℝ) : ℂ :=
  ∑ p ∈ mrtPrimeBand L ((N : ℝ) / 2),
    (Real.log (p : ℝ) : ℂ) * f p *
      (halaszPrimeConvolution f (N / p) / (Real.log ((N : ℝ) / p) : ℂ))

lemma halasz_divisor_cutoff {N p : ℕ} (hp : 0 < p) (hpN : 2 * p ≤ N) :
    1 ≤ N / p ∧ ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p ∧
      (N : ℝ) / p ≤ 2 * ((N / p : ℕ) : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hM : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp).mpr (by omega)
  refine ⟨hM, ?_, ?_⟩
  · apply (le_div_iff₀ hp0).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  · have hmod : ((N % p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt N hp
    have hid : ((N % p : ℕ) : ℝ) + (p : ℝ) * ((N / p : ℕ) : ℝ) = N := by
      exact_mod_cast Nat.mod_add_div N p
    have hM1 : (1 : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hM
    apply (div_le_iff₀ hp0).mpr
    nlinarith

theorem halasz_double_convolution_error (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    ‖halaszPrimeBandConvolution f N L ((N : ℝ) / 2) -
        halaszDoubleConvolution f N L‖ ≤
      halaszInnerErrorConstant * (N : ℝ) *
        ∑ p ∈ mrtPrimeBand L ((N : ℝ) / 2),
          Real.log (p : ℝ) / ((p : ℝ) * Real.log ((N : ℝ) / p)) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := by linarith
  unfold halaszPrimeBandConvolution halaszDoubleConvolution halaszPrimeTerm
  rw [← sum_sub_distrib, mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  have hprime := mrtPrimeBand_prime hp
  have hb := mrtPrimeBand_bounds hL0 (by positivity : (0 : ℝ) ≤ (N : ℝ) / 2) hp
  have hpN : 2 * p ≤ N := by exact_mod_cast (show 2 * (p : ℝ) ≤ N by linarith)
  obtain ⟨hM, hMx, hxM⟩ := halasz_divisor_cutoff hprime.pos hpN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hx : 1 < (N : ℝ) / p := by
    have hh : (2 : ℝ) ≤ (N : ℝ) / p := (le_div_iff₀ hp0).mpr (by linarith)
    linarith
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
  rw [← mul_sub, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog]
  calc
    _ ≤ Real.log (p : ℝ) * 1 *
        (halaszInnerErrorConstant * ((N : ℝ) / p) / Real.log ((N : ℝ) / p)) := by
      gcongr
      · exact hf p hprime.pos
      · exact halasz_real_inner_approximation f hf hmul (N / p) hM hx hMx hxM
    _ = _ := by ring

end TwoPointCorrelations

end OAI
