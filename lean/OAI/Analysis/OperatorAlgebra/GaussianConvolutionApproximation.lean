import OAI.Analysis.OperatorAlgebra.ScalarTranslationConvolution
import OAI.Analysis.OperatorAlgebra.SmallTimeOperatorAverage

namespace OAI

/-! Actual integrable L² Gaussian convolution kernels give a uniformly
contractive strong approximate identity on vector-valued L². -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace WeakPureInfiniteness

lemma realGaussianDensity_continuous : Continuous realGaussianDensity := by
  unfold realGaussianDensity
  fun_prop

lemma realGaussianDensity_bound (t : ℝ) : realGaussianDensity t ≤ 1 / Real.sqrt Real.pi := by
  exact div_le_div_of_nonneg_right
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg t))) (Real.sqrt_nonneg _)

def gaussianConvolutionKernel (n : ℕ) (t : ℝ) : ℂ :=
  ((n + 1 : ℝ) : ℂ) * (realGaussianDensity ((n + 1 : ℝ) * t) : ℂ)

lemma gaussianConvolutionKernel_continuous (n : ℕ) : Continuous (gaussianConvolutionKernel n) :=
  continuous_const.mul (Complex.continuous_ofReal.comp
    (realGaussianDensity_continuous.comp (continuous_const.mul continuous_id)))

lemma gaussianConvolutionKernel_integrable (n : ℕ) : Integrable (gaussianConvolutionKernel n) := by
  have hN : (n + 1 : ℝ) ≠ 0 := by positivity
  have hi := (integrable_comp_mul_left_iff realGaussianDensity hN).mpr realGaussianDensity_integrable
  exact hi.ofReal.const_mul ((n + 1 : ℝ) : ℂ)

lemma gaussianConvolutionKernel_bound (n : ℕ) (t : ℝ) :
    ‖gaussianConvolutionKernel n t‖ ≤ (n + 1 : ℝ) / Real.sqrt Real.pi := by
  change ‖((n + 1 : ℝ) : ℂ) * (realGaussianDensity ((n + 1 : ℝ) * t) : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (n + 1 : ℝ)),
    abs_of_nonneg (realGaussianDensity_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (realGaussianDensity_bound _) (by positivity)).trans_eq
    (by ring)

lemma gaussianConvolutionKernel_memLp (n : ℕ) :
    MemLp (gaussianConvolutionKernel n) 2 (volume : Measure ℝ) := by
  apply (memLp_two_iff_integrable_sq_norm
    (gaussianConvolutionKernel_continuous n).aestronglyMeasurable).mpr
  apply ((gaussianConvolutionKernel_integrable n).norm.const_mul
    ((n + 1 : ℝ) / Real.sqrt Real.pi)).mono'
    ((gaussianConvolutionKernel_continuous n).norm.pow 2).aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right (gaussianConvolutionKernel_bound n t) (norm_nonneg _)

def gaussianConvolutionVector (n : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (gaussianConvolutionKernel_memLp n).toLp (gaussianConvolutionKernel n)

lemma gaussianConvolutionVector_ae (n : ℕ) :
    gaussianConvolutionVector n =ᵐ[volume] gaussianConvolutionKernel n := MemLp.coeFn_toLp _

lemma gaussianConvolutionVector_integrable (n : ℕ) :
    Integrable (gaussianConvolutionVector n : ℝ → ℂ) :=
  (gaussianConvolutionKernel_integrable n).congr (gaussianConvolutionVector_ae n).symm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma gaussianConvolutionKernel_apply (n : ℕ) (f : Lp H 2 (volume : Measure ℝ)) :
    integratedModularTranslation (gaussianConvolutionKernel n) (gaussianConvolutionKernel_integrable n) f =
      smallTimeOperatorAverage (modularLpTranslateOperator (H := H))
        continuous_modularLpTranslate 1 modularLpTranslate_opNorm_le n f := by
  let N : ℝ := n + 1
  have hN : 0 < N := by dsimp [N]; positivity
  change (∫ t : ℝ, ((N : ℂ) * (realGaussianDensity (N * t) : ℂ)) •
      modularLpTranslate volume t f) =
    ∫ t : ℝ, (realGaussianDensity t : ℂ) • modularLpTranslate volume (t / N) f
  calc
    _ = (N : ℂ) • ∫ t : ℝ, (realGaussianDensity (N * t) : ℂ) •
        modularLpTranslate volume ((N * t) / N) f := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [mul_div_cancel_left₀ t hN.ne', smul_smul]
    _ = (N : ℂ) • (|N⁻¹| •
        ∫ t : ℝ, (realGaussianDensity t : ℂ) • modularLpTranslate volume (t / N) f) := by
      exact congrArg (fun v : Lp H 2 (volume : Measure ℝ) => (N : ℂ) • v)
        (Measure.integral_comp_mul_left
          (fun t : ℝ => (realGaussianDensity t : ℂ) • modularLpTranslate volume (t / N) f) N)
    _ = _ := by
      rw [abs_of_pos (inv_pos.mpr hN)]
      change (N : ℂ) • ((N⁻¹ : ℝ) : ℂ) •
        (∫ t : ℝ, (realGaussianDensity t : ℂ) • modularLpTranslate volume (t / N) f) = _
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hN.ne', Complex.ofReal_one, one_smul]

omit [CompleteSpace H] in
lemma gaussianConvolutionVector_apply (n : ℕ) (f : Lp H 2 (volume : Measure ℝ)) :
    integratedModularTranslation (gaussianConvolutionVector n) (gaussianConvolutionVector_integrable n) f =
      smallTimeOperatorAverage (modularLpTranslateOperator (H := H))
        continuous_modularLpTranslate 1 modularLpTranslate_opNorm_le n f := by
  rw [← gaussianConvolutionKernel_apply]
  apply integral_congr_ae
  filter_upwards [gaussianConvolutionVector_ae n] with t ht
  rw [ht]

lemma gaussianConvolutionVector_strong (f : Lp H 2 (volume : Measure ℝ)) :
    Tendsto (fun n => integratedModularTranslation (gaussianConvolutionVector n)
      (gaussianConvolutionVector_integrable n) f) atTop (𝓝 f) := by
  have h := smallTimeOperatorAverage_strong (modularLpTranslateOperator (H := H))
    continuous_modularLpTranslate 1 modularLpTranslate_opNorm_le f
  simpa only [gaussianConvolutionVector_apply, modularLpTranslateOperator_apply,
    modularLpTranslate_zero] using h

end WeakPureInfiniteness

end

end OAI
