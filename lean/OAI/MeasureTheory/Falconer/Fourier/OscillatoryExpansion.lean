import OAI.MeasureTheory.Falconer.Fourier.EndpointTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-!
# Oscillatory spatial expansion before absolute values

The product of an endpoint transform and a conjugate transform is written
as the exact two-point integral with displacement phase. The identity uses
the original spatial measures and does not assume spatial smoothness.
-/

namespace Falconer
open MeasureTheory
open scoped ComplexConjugate

theorem exponential_mul_conj (s t : ℝ) :
    Complex.exp (Complex.I * (s : ℂ)) * star (Complex.exp (Complex.I * (t : ℂ))) =
      Complex.exp (Complex.I * ((s-t : ℝ) : ℂ)) := by
  rw [show star (Complex.exp (Complex.I * (t : ℂ))) =
      Complex.exp (-Complex.I * (t : ℂ)) by simp [← Complex.exp_conj]]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem endpointTransform_mul_star {d : ℕ}
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M P : ℝ) (b c : Space d → Sphere d → ℂ) (r : ℝ) (w : Sphere d) :
    endpointTransform μ M b r w * star (endpointTransform ν P c r w) =
      (M⁻¹ * P⁻¹) • ∫ z : Space d × Space d,
        Complex.exp (Complex.I * ((r * inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ)) *
          (b z.1 w * star (c z.2 w)) ∂μ.prod ν := by
  have hid (x y : Space d) :
      (Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) x : ℂ)) * b x w) *
        star (Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) y : ℂ)) * c y w) =
      Complex.exp (Complex.I * ((r * inner ℝ (w : Space d) (x-y) : ℝ) : ℂ)) *
        (b x w * star (c y w)) := by
    rw [star_mul]
    have he := exponential_mul_conj (r * inner ℝ (w : Space d) x)
      (r * inner ℝ (w : Space d) y)
    push_cast at he
    rw [show r * inner ℝ (w : Space d) (x-y) =
      r * inner ℝ (w : Space d) x - r * inner ℝ (w : Space d) y by
        rw [inner_sub_right, mul_sub]]
    push_cast
    rw [← he]
    ring_nf
  simp only [endpointTransform, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    smul_smul]
  rw [mul_comm P⁻¹ M⁻¹]
  congr 1
  change _ * conj (∫ x, _ ∂ν) = _
  rw [← integral_conj, ← integral_prod_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => hid z.1 z.2)

/-- Equation `graph:phase`, with four possibly different endpoint laws and
with the symbols retained inside the original spatial integral. -/
theorem endpointTransform_four_point {d : ℕ}
    (μ μ' ν ν' : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (M M' P P' : ℝ) (b b' c c' : Space d → Sphere d → ℂ)
    (r : ℝ) (w v : Sphere d) :
    (endpointTransform μ M b r w * endpointTransform ν P c r v) *
      star (endpointTransform μ' M' b' r w * endpointTransform ν' P' c' r v) =
    ((M⁻¹ * M'⁻¹) * (P⁻¹ * P'⁻¹)) •
      ∫ z : (Space d × Space d) × (Space d × Space d),
        Complex.exp (Complex.I * ((r *
          (inner ℝ (w : Space d) (z.1.1-z.1.2) +
           inner ℝ (v : Space d) (z.2.1-z.2.2)) : ℝ) : ℂ)) *
          ((b z.1.1 w * star (b' z.1.2 w)) * (c z.2.1 v * star (c' z.2.2 v)))
        ∂(μ.prod μ').prod (ν.prod ν') := by
  rw [show (endpointTransform μ M b r w * endpointTransform ν P c r v) *
      star (endpointTransform μ' M' b' r w * endpointTransform ν' P' c' r v) =
      (endpointTransform μ M b r w * star (endpointTransform μ' M' b' r w)) *
      (endpointTransform ν P c r v * star (endpointTransform ν' P' c' r v)) by
        rw [star_mul]; ring]
  rw [endpointTransform_mul_star, endpointTransform_mul_star,
    smul_mul_smul_comm, ← integral_prod_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  have he : Complex.exp (Complex.I * ((r *
      (inner ℝ (w : Space d) (z.1.1-z.1.2) +
       inner ℝ (v : Space d) (z.2.1-z.2.2)) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((r * inner ℝ (w : Space d) (z.1.1-z.1.2) : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((r * inner ℝ (v : Space d) (z.2.1-z.2.2) : ℝ) : ℂ)) := by
    rw [mul_add, Complex.ofReal_add, mul_add, Complex.exp_add]
  rw [he]
  ring

end Falconer

end OAI
