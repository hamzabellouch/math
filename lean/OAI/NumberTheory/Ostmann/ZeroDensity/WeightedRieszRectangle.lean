import OAI.NumberTheory.Ostmann.ZeroDensity.RieszLeftEstimate
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszHorizontalEstimate

namespace OAI

/-! # Weighted Riesz edge bounds and a retained residue -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

theorem weightedRiesz_left_segment_bound : ∃ K : ℝ, 0 < K ∧
    ∀ (f : ℂ → ℂ) (X a T M : ℝ), 0 < X → 1 / 2 ≤ a → 0 ≤ M →
      (∀ t ∈ Icc (-T) T, ‖f (rieszMellinLine a t)‖ ≤ M) →
      ‖∫ t in Icc (-T) T, f (rieszMellinLine a t) * rieszVerticalWeight X a t‖ ≤ K * M * X ^ a := by
  let J := ∫ t : ℝ, rieszLineMajorant t
  have hJ : 0 ≤ J := integral_nonneg rieszLineMajorant_nonneg
  refine ⟨J + 1, by linarith, ?_⟩
  intro f X a T M hX ha hM hb
  have hg : Integrable (fun t : ℝ => (M * X ^ a) * rieszLineMajorant t) :=
    rieszLineMajorant_integrable.const_mul _
  have hnorm : ‖∫ t in Icc (-T) T, f (rieszMellinLine a t) * rieszVerticalWeight X a t‖ ≤
      ∫ t in Icc (-T) T, (M * X ^ a) * rieszLineMajorant t := by
    apply norm_integral_le_of_norm_le hg.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hk := rieszMellinKernel_half_strip (rieszMellinLine a t) (by simpa using ha)
    simp only [rieszMellinLine, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
      zero_add] at hk
    rw [norm_mul, rieszVerticalWeight_norm X a t hX]
    have hh := mul_le_mul (hb t ht) (mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hX.le a))
      (by positivity) hM
    exact hh.trans_eq (by ring)
  have hfull := setIntegral_le_integral hg
    (Filter.Eventually.of_forall (fun t => mul_nonneg (by positivity) (rieszLineMajorant_nonneg t)))
    (s := Icc (-T) T)
  simp only [integral_const_mul] at hnorm hfull
  apply (hnorm.trans hfull).trans
  dsimp only [J] at hJ ⊢
  nlinarith [mul_nonneg hM (Real.rpow_nonneg hX.le a)]

theorem weightedRiesz_horizontal_segment_bound (f : ℂ → ℂ)
    (X a b t M : ℝ) (hX : 1 ≤ X) (hab : a ≤ b) (ht : 0 < |t|) (hM : 0 ≤ M)
    (hb : ∀ σ ∈ Icc a b, ‖f ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M) :
    ‖∫ σ in a..b, f ((σ : ℂ) + (t : ℂ) * I) *
        rieszContourWeight X ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      (M * X ^ b / t ^ 2) * (b - a) := by
  have hXp : 0 < X := by linarith
  have hpoint : ∀ σ ∈ Ι a b,
      ‖f ((σ : ℂ) + (t : ℂ) * I) *
        rieszContourWeight X ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M * X ^ b / t ^ 2 := by
    intro σ hσ
    have hσ' : σ ∈ Icc a b := by
      have hh := uIoc_subset_uIcc hσ
      rwa [uIcc_of_le hab] at hh
    have hk := rieszMellinKernel_im_bound ((σ : ℂ) + (t : ℂ) * I) (by simpa using ht)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, sq_abs] at hk
    have hx : X ^ σ ≤ X ^ b := Real.rpow_le_rpow_of_exponent_le hX hσ'.2
    rw [norm_mul, rieszContourWeight, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hXp]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero]
    have hh := mul_le_mul (hb σ hσ') (mul_le_mul hx hk (norm_nonneg _) (Real.rpow_nonneg hXp.le _))
      (by positivity) hM
    exact hh.trans_eq (by ring)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hi

theorem rectangle_vertical_shift_residue_norm_bound (f : ℂ → ℂ) (a b c d : ℝ)
    (z : ℂ) (hzero : rectangleBoundaryIntegral f a b c d = I * z) :
    ‖(∫ y in c..d, f ((b : ℂ) + (y : ℂ) * I)) - z‖ ≤
      ‖∫ y in c..d, f ((a : ℂ) + (y : ℂ) * I)‖ +
      ‖∫ x in a..b, f ((x : ℂ) + (d : ℂ) * I)‖ +
      ‖∫ x in a..b, f ((x : ℂ) + (c : ℂ) * I)‖ := by
  let R := ∫ y in c..d, f ((b : ℂ) + (y : ℂ) * I)
  let L := ∫ y in c..d, f ((a : ℂ) + (y : ℂ) * I)
  let U := ∫ x in a..b, f ((x : ℂ) + (d : ℂ) * I)
  let D := ∫ x in a..b, f ((x : ℂ) + (c : ℂ) * I)
  have he : I * (R - z) = I * L + U - D := by
    dsimp [rectangleBoundaryIntegral] at hzero
    dsimp [R, L, U, D]
    linear_combination hzero
  change ‖R - z‖ ≤ ‖L‖ + ‖U‖ + ‖D‖
  calc
    ‖R - z‖ = ‖I * (R - z)‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    _ = ‖I * L + U - D‖ := by rw [he]
    _ ≤ ‖I * L + U‖ + ‖D‖ := norm_sub_le _ _
    _ ≤ (‖I * L‖ + ‖U‖) + ‖D‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by rw [norm_mul, Complex.norm_I, one_mul]

end Ostmann

end OAI
