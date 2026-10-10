import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import OAI.NumberTheory.Ostmann.Construction.PositiveFourierCutoff
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticLogTranslation
import OAI.NumberTheory.Ostmann.Arithmetic.ScaledPoisson

namespace OAI

/-! # Exact Fourier localization for finite Dirichlet polynomials -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform

noncomputable def densityLocalizedPolynomial {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (a : ι → ℂ) (freq : ι → ℝ) : 𝓢(ℝ, ℂ) :=
  ∑ j, a j • (positiveDilate W h⁻¹ (inv_pos.mpr hh)).compSubConstCLM ℂ (freq j)

 theorem densityLocalizedPolynomial_apply {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (a : ι → ℂ) (freq : ι → ℝ) (x : ℝ) :
    densityLocalizedPolynomial W h hh a freq x =
      ∑ j, a j * W ((x - freq j) / h) := by
  simp only [densityLocalizedPolynomial, sum_apply, smul_apply,
    SchwartzMap.compSubConstCLM_apply, positiveDilate_apply, smul_eq_mul]
  congr 1
  funext j
  rw [div_eq_inv_mul]

 theorem densityLocalizedPolynomial_fourier {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    𝓕 (densityLocalizedPolynomial W h hh a freq) t =
      (h : ℂ) * 𝓕 W (h * t) * ∑ j, a j * realAdditivePhase (-(freq j * t)) := by
  simp only [densityLocalizedPolynomial, FourierTransform.fourier_sum, FourierTransform.fourier_smul,
    sum_apply, smul_apply, quadratic_fourier_translate,
    positiveDilate_fourier, div_inv_eq_mul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm t h]
  push_cast
  rw [inv_inv]
  ring

 theorem densityLocalizedPolynomial_plancherel {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (h : ℝ) (hh : 0 < h) (a : ι → ℂ) (freq : ι → ℝ) :
    (∫ t : ℝ, h ^ 2 * ‖𝓕 W (h * t)‖ ^ 2 *
      ‖∑ j, a j * realAdditivePhase (-(freq j * t))‖ ^ 2) =
        ∫ x : ℝ, ‖∑ j, a j * W ((x - freq j) / h)‖ ^ 2 := by
  have H := SchwartzMap.integral_norm_sq_fourier (densityLocalizedPolynomial W h hh a freq)
  simpa only [densityLocalizedPolynomial_fourier, densityLocalizedPolynomial_apply,
    norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh] using H

 theorem density_localized_pointwise_bound {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (c h T : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hwindow : h * T ≤ 1) (hW : ∀ t, |t| ≤ 1 → c ≤ ‖𝓕 W t‖)
    (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) (ht : |t| ≤ T) :
    h ^ 2 * c ^ 2 * ‖∑ j, a j * realAdditivePhase (-(freq j * t))‖ ^ 2 ≤
      ‖𝓕 (densityLocalizedPolynomial W h hh a freq) t‖ ^ 2 := by
  have ht' : |h * t| ≤ 1 := by
    rw [abs_mul, abs_of_pos hh]
    exact (mul_le_mul_of_nonneg_left ht hh.le).trans hwindow
  have hw := hW (h * t) ht'
  rw [densityLocalizedPolynomial_fourier, norm_mul, norm_mul, mul_pow, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  gcongr

end Ostmann

end OAI
