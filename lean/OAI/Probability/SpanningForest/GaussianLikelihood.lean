import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem336.GaussianObservation

theorem pdf_binary_shift (v : ℝ≥0) (hv : v ≠ 0) (x y : ℝ)
    (hx : x = 0 ∨ x = 1) :
    gaussianPDFReal ((v : ℝ) * x) v y =
      gaussianPDFReal 0 v y * Real.exp ((y - (v : ℝ) / 2) * x) := by
  rcases hx with rfl | rfl
  · simp
  · have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    have hexp : -(y - (v : ℝ)) ^ 2 / (2 * (v : ℝ)) =
        -y ^ 2 / (2 * (v : ℝ)) + (y - (v : ℝ) / 2) := by
      field_simp
      ring
    simp only [mul_one, gaussianPDFReal, sub_zero]
    rw [hexp, Real.exp_add]
    ring

theorem pdf_binary_shift_ennreal (v : ℝ≥0) (hv : v ≠ 0) (x y : ℝ)
    (hx : x = 0 ∨ x = 1) :
    gaussianPDF ((v : ℝ) * x) v y =
      gaussianPDF 0 v y * ENNReal.ofReal (Real.exp ((y - (v : ℝ) / 2) * x)) := by
  simp only [gaussianPDF, pdf_binary_shift v hv x y hx,
    ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v y)]

theorem gaussian_binary_shift_withDensity (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ)
    (hx : x = 0 ∨ x = 1) :
    gaussianReal ((v : ℝ) * x) v =
      (gaussianReal 0 v).withDensity
        (fun y => ENNReal.ofReal (Real.exp ((y - (v : ℝ) / 2) * x))) := by
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    ← withDensity_mul volume (measurable_gaussianPDF 0 v) (by fun_prop)]
  congr 1
  funext y
  exact pdf_binary_shift_ennreal v hv x y hx

theorem gaussian_binary_shift_withDensity_all (v : ℝ≥0) (x : ℝ)
    (hx : x = 0 ∨ x = 1) :
    gaussianReal ((v : ℝ) * x) v =
      (gaussianReal 0 v).withDensity
        (fun y => ENNReal.ofReal (Real.exp ((y - (v : ℝ) / 2) * x))) := by
  by_cases hv : v = 0
  · subst v
    simp [dirac_withDensity]
  · exact gaussian_binary_shift_withDensity v hv x hx

theorem likelihood_lintegral_eq_one (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ)
    (hx : x = 0 ∨ x = 1) :
    (∫⁻ y, ENNReal.ofReal (Real.exp ((y - (v : ℝ) / 2) * x))
      ∂gaussianReal 0 v) = 1 := by
  have h := congrArg (fun μ : Measure ℝ => μ Set.univ)
    (gaussian_binary_shift_withDensity v hv x hx)
  simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using h.symm

theorem gaussian_binary_shift_absolutelyContinuous (v : ℝ≥0) (hv : v ≠ 0)
    (x : ℝ) (hx : x = 0 ∨ x = 1) :
    gaussianReal ((v : ℝ) * x) v ≪ gaussianReal 0 v := by
  rw [gaussian_binary_shift_withDensity v hv x hx]
  exact withDensity_absolutelyContinuous _ _

theorem rnDeriv_gaussian_binary_shift (v : ℝ≥0) (hv : v ≠ 0)
    (x : ℝ) (hx : x = 0 ∨ x = 1) :
    (gaussianReal ((v : ℝ) * x) v).rnDeriv (gaussianReal 0 v) =ᵐ[gaussianReal 0 v]
      (fun y => ENNReal.ofReal (Real.exp ((y - (v : ℝ) / 2) * x))) := by
  rw [gaussian_binary_shift_withDensity v hv x hx]
  exact Measure.rnDeriv_withDensity _ (by fun_prop)

theorem prod_pdf_binary_shift {ι : Type*} (s : Finset ι) (v : ℝ≥0)
    (hv : v ≠ 0) (x y : ι → ℝ) (hx : ∀ i ∈ s, x i = 0 ∨ x i = 1) :
    (∏ i ∈ s, gaussianPDFReal ((v : ℝ) * x i) v (y i)) =
      (∏ i ∈ s, gaussianPDFReal 0 v (y i)) *
        Real.exp (∑ i ∈ s, (y i - (v : ℝ) / 2) * x i) := by
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact pdf_binary_shift v hv (x i) (y i) (hx i hi)

end Problem336.GaussianObservation

end

end OAI
