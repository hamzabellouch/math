import OAI.NumberTheory.JointDickman.Counting.CenteredShortCoefficients

namespace OAI

/-! # Centered short-average energy for the real mean-comparison application -/
namespace JointDickman
open Finset MeasureTheory PublishedInputs

theorem complexShortAverage_sub_sq_integrable (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {H : ℝ} (hH : 0 < H) (c : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun x => ‖complexShortAverage f H x - c‖ ^ 2) volume a b := by
  let K : ℝ := (⌊max a b + H⌋₊ : ℝ) / H + ‖c‖
  have hm := (((measurable_complexShortAverage f H).sub_const c).norm.pow_const 2)
  refine (intervalIntegrable_const (c := K ^ 2)).mono_fun' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  have hh : ‖complexShortAverage f H x - c‖ ≤ K :=
    (norm_sub_le _ _).trans (add_le_add (norm_complexShortAverage_le f hf hH hx.2) le_rfl)
  simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using
    pow_le_pow_left₀ (norm_nonneg _) hh 2

/-- Passing to centered coefficients has only an `O(1/H^2)` energy cost. -/
theorem centeredShort_energy_le (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {c : ℂ} (hc : ‖c‖ ≤ 2) {X H : ℝ} (hX : 0 < X) (hH : 0 < H) :
    (1 / X) * (∫ x in X..2 * X, ‖complexShortAverage f H x - c‖ ^ 2) ≤
      18 * ((1 / X) * (∫ x in X..2 * X,
        ‖complexShortAverage (centeredShortCoefficients f c) H x‖ ^ 2)) + 8 / H ^ 2 := by
  let g := centeredShortCoefficients f c
  have hg : ∀ n, ‖g n‖ ≤ 1 := centeredShortCoefficients_norm_le f hf hc
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc X (2 * X)) :
      ‖complexShortAverage f H x - c‖ ^ 2 ≤
        18 * ‖complexShortAverage g H x‖ ^ 2 + 8 / H ^ 2 := by
    have hh := centeredShortCoefficients_short_error f hc (hX.trans_le hx.1).le hH
    have hn := norm_nonneg (complexShortAverage f H x - c)
    have hg := norm_nonneg (complexShortAverage g H x)
    have he : 0 ≤ 2 / H := by positivity
    have hsq : ‖complexShortAverage f H x - c‖ ^ 2 ≤
        18 * ‖complexShortAverage g H x‖ ^ 2 + 2 * (2 / H) ^ 2 := by
      nlinarith [sq_nonneg (3 * ‖complexShortAverage g H x‖ - 2 / H)]
    convert hsq using 1
    ring
  have hi := intervalIntegral.integral_mono_on (show X ≤ 2 * X by linarith)
    (complexShortAverage_sub_sq_integrable f hf hH c X (2 * X))
    (((complexShortAverage_sq_integrable g hg hH X (2 * X)).const_mul 18).add
      intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add
      ((complexShortAverage_sq_integrable g hg hH X (2 * X)).const_mul 18)
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hi
  have hscaled := mul_le_mul_of_nonneg_left hi (show 0 ≤ 1 / X by positivity)
  convert hscaled using 1
  simp only [smul_eq_mul]
  field_simp
  ring

theorem centeredShortAverage_dyadic_energy (η : ℝ) (hη : 0 < η) (hηhalf : η < 1/2)
    (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ArithmeticFunction ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ c : ℂ, ‖c‖ ≤ 2 → ∀ X H : ℝ, 0 < X → 1 ≤ H → H ≤ X →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      (∀ T : ℝ, 1 ≤ T →
        (∫ t in -T..T, ‖mellinPolynomial (Ioc ⌊X⌋₊ ⌊4 * X⌋₊)
          (centeredShortCoefficients f c) t‖ ^ 2) ≤ A + B * T) →
      (1 / X) * (∫ x in X..2 * X, ‖complexShortAverage f H x - c‖ ^ 2) ≤
        C * (A + B * X / H) +
          36 * (3 / (m : ℝ) + 11 / H + H / X + 1 / X + 16 * η) ^ 2 + 8 / H ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := shortAverage_dyadic_energy η hη hηhalf m hm
  refine ⟨18 * C, by positivity, ?_⟩
  intro f hf c hc X H hX hH hHX A B hA hB hspectral
  have hg := centeredShortCoefficients_norm_le f hf hc
  have hh := hbound (centeredShortCoefficients f c) hg X H hX hH hHX A B hA hB hspectral
  have ht := centeredShort_energy_le f hf hc hX (by linarith : 0 < H)
  nlinarith

end JointDickman

end OAI
