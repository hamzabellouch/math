import OAI.Analysis.KadisonKastler.PoissonVectorAverage
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace OAI

/-! # The actual half-plane Poisson kernel

The fixed-law vector averages agree with integration against
`r / (π ((t-s)²+r²))` for every positive height.
-/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def realPoissonKernel (t r s : ℝ) : ℝ := r / (Real.pi * ((t - s) ^ 2 + r ^ 2))

omit [CompleteSpace E] in
theorem integral_standardCauchy (f : ℝ → E) :
    (∫ s, f s ∂cauchyMeasure 0 1) =
      ∫ s, realPoissonKernel 0 1 s • f s := by
  rw [cauchyMeasure_of_scale_ne_zero 0 (by norm_num),
    integral_withDensity_eq_integral_toReal_smul (measurable_cauchyPDF 0 1)
      (ae_of_all _ fun s => ENNReal.ofReal_lt_top)]
  congr 1
  funext s
  congr 1
  rw [cauchyPDF, ENNReal.toReal_ofReal (cauchyPDF_pos 0 (by norm_num) s).le]
  simp only [cauchyPDFReal, NNReal.coe_one, sub_zero, mul_one, one_pow,
    realPoissonKernel, zero_sub, neg_sq, one_div, mul_inv_rev]
  ring

private theorem realPoissonKernel_affine {r : ℝ} (hr : 0 < r) (t s : ℝ) :
    r * realPoissonKernel t r (t + r * s) = realPoissonKernel 0 1 s := by
  have h₁ : (t - (t + r * s)) ^ 2 + r ^ 2 ≠ 0 := by positivity
  have h₂ : (0 - s) ^ 2 + (1 : ℝ) ^ 2 ≠ 0 := by positivity
  unfold realPoissonKernel
  field_simp [Real.pi_ne_zero, h₁, h₂]
  ring

omit [CompleteSpace E] in
theorem integral_standardCauchy_affine (f : ℝ → E) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ s, f (t + r * s) ∂cauchyMeasure 0 1) =
      ∫ s, realPoissonKernel t r s • f s := by
  rw [integral_standardCauchy]
  let g : ℝ → E := fun s => realPoissonKernel t r s • f s
  have he (s : ℝ) : realPoissonKernel 0 1 s • f (t + r * s) =
      r • g (t + r * s) := by
    dsimp only [g]
    rw [smul_smul, realPoissonKernel_affine hr]
  simp_rw [he]
  rw [integral_smul, Measure.integral_comp_mul_left (fun s => g (t + s)) r,
    integral_add_left_eq_self, smul_smul, abs_of_pos (inv_pos.mpr hr),
    mul_inv_cancel₀ hr.ne', one_smul]

theorem poissonVectorAverage_apply_eq_integral {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, Continuous (fun s => F s x))
    (C : ℝ) (hC : ∀ s, ‖F s‖ ≤ C) (t : ℝ) {r : ℝ} (hr : 0 < r) (x : H) :
    poissonVectorAverage F hF C hC t r x =
      ∫ s, realPoissonKernel t r s • F s x :=
  integral_standardCauchy_affine (fun s => F s x) t hr

end

end KadisonKastler

end OAI
