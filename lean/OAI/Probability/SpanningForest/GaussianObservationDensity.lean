import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem336

theorem gaussianPDFReal_binary_observation (t : ℝ≥0) (ht : t ≠ 0)
    (x y : ℝ) (hx : x = 0 ∨ x = 1) :
    gaussianPDFReal ((t : ℝ) * x) t y =
      gaussianPDFReal 0 t y * Real.exp ((y - (t : ℝ) / 2) * x) := by
  rcases hx with rfl | rfl
  · simp
  · have ht' : (t : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr ht
    have hexp : -(y - (t : ℝ)) ^ 2 / (2 * (t : ℝ)) =
        -y ^ 2 / (2 * (t : ℝ)) + (y - (t : ℝ) / 2) := by
      field_simp
      ring
    simp only [mul_one, gaussianPDFReal, sub_zero, hexp, Real.exp_add]
    ring

theorem gaussianPDFReal_finite_binary_observation {ι : Type*}
    (s : Finset ι) (t : ℝ≥0) (ht : t ≠ 0) (x y : ι → ℝ)
    (hx : ∀ i ∈ s, x i = 0 ∨ x i = 1) :
    (∏ i ∈ s, gaussianPDFReal ((t : ℝ) * x i) t (y i)) =
      (∏ i ∈ s, gaussianPDFReal 0 t (y i)) *
        Real.exp (∑ i ∈ s, (y i - (t : ℝ) / 2) * x i) := by
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i hi => gaussianPDFReal_binary_observation t ht _ _ (hx i hi))

theorem gaussianPDF_binary_observation (t : ℝ≥0) (ht : t ≠ 0)
    (x y : ℝ) (hx : x = 0 ∨ x = 1) :
    gaussianPDF ((t : ℝ) * x) t y =
      gaussianPDF 0 t y * ENNReal.ofReal (Real.exp ((y - (t : ℝ) / 2) * x)) := by
  unfold gaussianPDF
  rw [gaussianPDFReal_binary_observation t ht x y hx,
    ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 t y)]

theorem gaussianReal_binary_observation (t : ℝ≥0) (ht : t ≠ 0)
    (x : ℝ) (hx : x = 0 ∨ x = 1) :
    gaussianReal ((t : ℝ) * x) t =
      (gaussianReal 0 t).withDensity
        (fun y => ENNReal.ofReal (Real.exp ((y - (t : ℝ) / 2) * x))) := by
  rw [gaussianReal_of_var_ne_zero _ ht, gaussianReal_of_var_ne_zero _ ht,
    ← withDensity_mul _ (measurable_gaussianPDF 0 t) (by fun_prop)]
  congr 1
  funext y
  exact gaussianPDF_binary_observation t ht x y hx

end Problem336

end

end OAI
