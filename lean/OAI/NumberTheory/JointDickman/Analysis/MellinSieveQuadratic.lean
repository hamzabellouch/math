import OAI.NumberTheory.JointDickman.Analysis.MellinSampleDuality
import OAI.NumberTheory.JointDickman.Analysis.SeparatedMellinKernel

namespace OAI

/-! # The positive continuous main term for the sparse-prime sieve -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations
open scoped ComplexConjugate

noncomputable def mellinSieveMainKernel (N t : ℝ) : ℂ :=
  Complex.exp (((-Real.log N*t : ℝ) : ℂ)*Complex.I) * ((4*N/(4+t^2) : ℝ) : ℂ)

noncomputable def mellinSieveMain (N : ℝ) (S : Finset ℝ) (b : ℝ → ℂ) : ℝ :=
  N * ∫ v : ℝ, Real.exp (-|v|/(1/2)) *
    ‖mrtExponentialPolynomial S (fun t => b t *
      Complex.exp (((-Real.log N*t : ℝ) : ℂ)*Complex.I)) (fun t => -t) v‖^2

lemma mellinSieveMain_nonneg {N : ℝ} (hN : 0 ≤ N) (S : Finset ℝ) (b : ℝ → ℂ) :
    0 ≤ mellinSieveMain N S b := by
  unfold mellinSieveMain
  apply mul_nonneg hN
  exact integral_nonneg (fun _ => by positivity)

lemma norm_mellinSieveMainKernel {N : ℝ} (hN : 0 ≤ N) (t : ℝ) :
    ‖mellinSieveMainKernel N t‖ = 4*N/(4+t^2) := by
  unfold mellinSieveMainKernel
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

lemma mellinSieveMain_eq (N : ℝ) (S : Finset ℝ) (b : ℝ → ℂ) :
    mellinSieveMain N S b = ∑ t ∈ S, ∑ u ∈ S,
      ((b t*conj (b u))*mellinSieveMainKernel N (t-u)).re := by
  unfold mellinSieveMain
  rw [mrt_weighted_mean_square S _ _ (by norm_num : (0:ℝ) < 1/2), mul_sum]
  apply sum_congr rfl
  intro t _
  rw [mul_sum]
  apply sum_congr rfl
  intro u _
  have hp := mrt_phase_pair (-Real.log N*t) (-Real.log N*u)
  rw [show -Real.log N*t - -Real.log N*u = -Real.log N*(t-u) by ring] at hp
  have he : (b t*Complex.exp (((-Real.log N*t : ℝ) : ℂ)*Complex.I))*
      conj (b u*Complex.exp (((-Real.log N*u : ℝ) : ℂ)*Complex.I)) =
      (b t*conj (b u))*Complex.exp (((-Real.log N*(t-u) : ℝ) : ℂ)*Complex.I) := by
    rw [map_mul, ← hp]
    ring
  rw [he]
  unfold mellinSieveMainKernel
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hden : 0 < 4+(t-u)^2 := by positivity
  field_simp
  ring

lemma mellinSieveMain_bound {N : ℝ} (hN : 0 ≤ N) (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) (b : ℝ → ℂ) :
    mellinSieveMain N S b ≤ 32*N*∑ t ∈ S, ‖b t‖^2 := by
  rw [mellinSieveMain_eq]
  calc
    _ ≤ ∑ t ∈ S, ∑ u ∈ S, ‖b t‖*‖b u‖*(4*N/(4+(t-u)^2)) := by
      apply sum_le_sum
      intro t _
      apply sum_le_sum
      intro u _
      simpa only [norm_mul, Complex.norm_conj, norm_mellinSieveMainKernel hN] using
        Complex.re_le_norm ((b t*conj (b u))*mellinSieveMainKernel N (t-u))
    _ ≤ _ := by
      apply mrt_symmetric_row_bound S _ (fun t => ‖b t‖) (32*N)
        (fun _ _ _ _ => by positivity) _ (fun t _ => separated_mellin_profile_rows S hsep hN t)
      intro t _ u _
      rw [show (t-u)^2 = (u-t)^2 by ring]

/-- The remainder of a finite quadratic form is bounded from its actual
pairwise kernel discrepancies. The sample count is exposed explicitly. -/
lemma mellin_quadratic_kernel_error (S : Finset ℝ) (b : ℝ → ℂ)
    (K L : ℝ → ℝ → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (herror : ∀ t ∈ S, ∀ u ∈ S, ‖K t u-L t u‖ ≤ δ) :
    |(∑ t ∈ S, ∑ u ∈ S, ((b t*conj (b u))*K t u).re) -
      (∑ t ∈ S, ∑ u ∈ S, ((b t*conj (b u))*L t u).re)| ≤
        δ*S.card*∑ t ∈ S, ‖b t‖^2 := by
  have he : (∑ t ∈ S, ∑ u ∈ S, ((b t*conj (b u))*K t u).re) -
      (∑ t ∈ S, ∑ u ∈ S, ((b t*conj (b u))*L t u).re) =
      (∑ t ∈ S, ∑ u ∈ S, (b t*conj (b u))*(K t u-L t u)).re := by
    simp only [Complex.re_sum, mul_sub, Complex.sub_re, sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ‖∑ t ∈ S, ∑ u ∈ S, (b t*conj (b u))*(K t u-L t u)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ t ∈ S, ∑ u ∈ S, ‖(b t*conj (b u))*(K t u-L t u)‖ :=
      (norm_sum_le _ _).trans (sum_le_sum fun t _ => norm_sum_le _ _)
    _ ≤ ∑ t ∈ S, ∑ u ∈ S, ‖b t‖*‖b u‖*δ := by
      apply sum_le_sum
      intro t ht
      apply sum_le_sum
      intro u hu
      simp only [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (herror t ht u hu) (by positivity)
    _ = δ*(∑ t ∈ S, ‖b t‖)^2 := by
      simp only [← sum_mul, ← mul_sum]
      ring
    _ ≤ _ := by
      have hh := sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun t => ‖b t‖)
      simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hh
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hδ

end JointDickman

end OAI
