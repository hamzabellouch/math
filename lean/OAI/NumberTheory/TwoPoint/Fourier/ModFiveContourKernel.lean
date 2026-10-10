import OAI.NumberTheory.TwoPoint.Fourier.ModFiveLFunctions
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import PrimeNumberTheoremAnd.Erdos970.ResidueCalcOnRectangles

namespace OAI

/-! Elementary kernel estimates for the finite Perron rectangle.
The vertical side has an integrable quadratic majorant, while each
horizontal side has the explicit inverse-square height saving.
-/

namespace TwoPointCorrelations

open Complex

noncomputable def modFivePerronKernel (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ s / (s * (s + 1))

lemma modFive_perron_denominator_vertical {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    (1 + t ^ 2) / 4 ≤
      ‖((σ : ℂ) + (t : ℂ) * Complex.I) *
        ((σ : ℂ) + (t : ℂ) * Complex.I + 1)‖ := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hnorm : ‖z‖ ≤ ‖z + 1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, z, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hnorm (norm_nonneg z)
  rw [← sq, Complex.sq_norm] at hm
  have hz : Complex.normSq z = σ ^ 2 + t ^ 2 := by
    simp [Complex.normSq_apply, z]
    ring
  rw [hz] at hm
  rw [norm_mul]
  change (1 + t ^ 2) / 4 ≤ ‖z‖ * ‖z + 1‖
  nlinarith [sq_nonneg t, sq_nonneg (σ - 1 / 2)]

lemma modFive_perron_denominator_horizontal (σ t : ℝ) :
    t ^ 2 ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) *
      ((σ : ℂ) + (t : ℂ) * Complex.I + 1)‖ := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have h1 : |t| ≤ ‖z‖ := by simpa [z] using Complex.abs_im_le_norm z
  have h2 : |t| ≤ ‖z + 1‖ := by simpa [z] using Complex.abs_im_le_norm (z + 1)
  have hm := mul_le_mul h1 h2 (abs_nonneg t) (norm_nonneg z)
  simpa only [← sq, sq_abs, norm_mul] using hm

lemma modFive_perron_kernel_vertical {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      4 * x ^ σ / (1 + t ^ 2) := by
  have hp : 0 < (1 + t ^ 2) / 4 := by positivity
  have hd := modFive_perron_denominator_vertical hσ t
  rw [modFivePerronKernel, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) hp hd).trans_eq (by
    field_simp)

lemma modFive_perron_kernel_horizontal {x : ℝ} (hx : 0 < x) (σ : ℝ)
    {t : ℝ} (ht : t ≠ 0) :
    ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ x ^ σ / t ^ 2 := by
  rw [modFivePerronKernel, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (sq_pos_of_ne_zero ht)
    (modFive_perron_denominator_horizontal σ t)

lemma modFivePerronKernel_integrable {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    MeasureTheory.Integrable (fun t : ℝ =>
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have h0 : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t ht
    have he := congrArg Complex.re ht
    norm_num at he
    linarith
  have h1 : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * Complex.I + 1 ≠ 0 := by
    intro t ht
    have he := congrArg Complex.re ht
    norm_num at he
    linarith
  have hcont : Continuous (fun t : ℝ =>
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    unfold modFivePerronKernel
    apply Continuous.div
    · exact (show Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) by
        fun_prop).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    · fun_prop
    · intro t
      exact mul_ne_zero (h0 t) (h1 t)
  have hmaj : MeasureTheory.Integrable (fun t : ℝ => 4 * x ^ σ / (1 + t ^ 2)) := by
    simpa only [div_eq_mul_inv] using
      (integrable_inv_one_add_sq.const_mul (4 * x ^ σ))
  apply hmaj.mono' hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall (modFive_perron_kernel_vertical hx hσ)

end TwoPointCorrelations

end OAI
