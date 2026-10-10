import OAI.Probability.InvariantIsing.Fields.FieldFoldedKernel
import Mathlib.Probability.Distributions.Gaussian.Real

namespace OAI

/-! Exact Gaussian folding and conditional sign factors. These identities
supply the folded transition and spin-mean kernel used in fld:radial. -/

noncomputable section
open scoped NNReal
open ProbabilityTheory

namespace InvariantIsing

lemma field_gaussian_pair_sum (v : ℝ≥0) (hv : v ≠ 0) (z u : ℝ) :
    gaussianPDFReal z v u + gaussianPDFReal z v (-u) =
      (2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * v))) *
        (Real.exp (-u ^ 2 / (2 * v)) * Real.cosh ((z / v) * u)) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have he₁ : -(u - z) ^ 2 / (2 * (v : ℝ)) =
      -z ^ 2 / (2 * v) + -u ^ 2 / (2 * v) + (z / v) * u := by
    field_simp [hv']
    ring
  have he₂ : -(-u - z) ^ 2 / (2 * (v : ℝ)) =
      -z ^ 2 / (2 * v) + -u ^ 2 / (2 * v) + -((z / v) * u) := by
    field_simp [hv']
    ring
  simp only [gaussianPDFReal, he₁, he₂, Real.exp_add, Real.cosh_eq]
  ring

lemma field_gaussian_pair_sign (v : ℝ≥0) (hv : v ≠ 0) (z u : ℝ) :
    gaussianPDFReal z v u - gaussianPDFReal z v (-u) =
      Real.tanh ((z / v) * u) * (gaussianPDFReal z v u + gaussianPDFReal z v (-u)) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  let t := (z / (v : ℝ)) * u
  let C := (Real.sqrt (2 * Real.pi * v))⁻¹ *
    Real.exp (-z ^ 2 / (2 * (v : ℝ))) * Real.exp (-u ^ 2 / (2 * (v : ℝ)))
  have he₁ : gaussianPDFReal z v u = C * Real.exp t := by
    have he : -(u - z) ^ 2 / (2 * (v : ℝ)) =
        -z ^ 2 / (2 * v) + -u ^ 2 / (2 * v) + t := by
      dsimp only [t]
      field_simp [hv']
      ring
    simp only [gaussianPDFReal, he, Real.exp_add, C]
    ring
  have he₂ : gaussianPDFReal z v (-u) = C * Real.exp (-t) := by
    have he : -(-u - z) ^ 2 / (2 * (v : ℝ)) =
        -z ^ 2 / (2 * v) + -u ^ 2 / (2 * v) + -t := by
      dsimp only [t]
      field_simp [hv']
      ring
    simp only [gaussianPDFReal, he, Real.exp_add, C]
    ring
  rw [he₁, he₂]
  change C * Real.exp t - C * Real.exp (-t) =
    Real.tanh t * (C * Real.exp t + C * Real.exp (-t))
  rw [Real.tanh_eq]
  field_simp [(add_pos (Real.exp_pos t) (Real.exp_pos (-t))).ne']

/-- An even terminal tilt cancels from the conditional sign law. -/
lemma field_even_tilt_conditional_sign (v : ℝ≥0) (hv : v ≠ 0)
    (ζ : ℝ) (F : ℝ → ℝ) (hF : Function.Even F) (z u : ℝ) :
    Real.exp (ζ * F u) * gaussianPDFReal z v u -
      Real.exp (ζ * F (-u)) * gaussianPDFReal z v (-u) =
      Real.tanh ((z / v) * u) *
        (Real.exp (ζ * F u) * gaussianPDFReal z v u +
          Real.exp (ζ * F (-u)) * gaussianPDFReal z v (-u)) := by
  rw [hF u]
  have he := field_gaussian_pair_sign v hv z u
  calc
    _ = Real.exp (ζ * F u) * (gaussianPDFReal z v u - gaussianPDFReal z v (-u)) := by ring
    _ = _ := by rw [he]; ring

end InvariantIsing

end

end OAI
