import OAI.Analysis.LipschitzHilbert.Fourier.PositiveConvolution
import OAI.Analysis.LipschitzHilbert.Fourier.LineKernelOscillation

namespace OAI

/-! Local Lipschitz continuity of the actual error convolution, obtained
by an integrable bound for kernel translations. -/

noncomputable section
open Set MeasureTheory

namespace LipschitzHilbert

theorem positiveConvolution_oscillation {f : ℝ → ℝ} (hf : Measurable f)
    {C l : ℝ} (_hC : 0 ≤ C) (hl : 0 < l) (hbound : ∀ s, ‖f s‖ ≤ C)
    (x y : ℝ) (hxy : |x-y| ≤ 2*l) :
    |positiveConvolution l f x - positiveConvolution l f y| ≤
      ((60 * Real.pi * C) / l) * |x-y| := by
  have hm : Integrable (fun s => ((C * (60/l^2)) * |x-y|) * lineEnvelope x l 1 s) :=
    (integrable_lineEnvelope_one x l hl).const_mul _
  have hp (s : ℝ) : ‖lineKernel l (x-s) * f s - lineKernel l (y-s) * f s‖ ≤
      ((C * (60/l^2)) * |x-y|) * lineEnvelope x l 1 s := by
    rw [← sub_mul, norm_mul, Real.norm_eq_abs]
    have h := mul_le_mul (lineKernel_translation_bound l s x y hl hxy) (hbound s)
      (norm_nonneg _) (mul_nonneg (by positivity : 0 ≤ (60/l^2) * |x-y|)
        (lineEnvelope_nonneg _ _ _ _))
    have heq : lineEnvelope s l 1 x = lineEnvelope x l 1 s := by
      simp only [lineEnvelope, div_pow, sub_sq_comm]
    rw [heq] at h
    apply h.trans_eq
    ring
  rw [positiveConvolution, positiveConvolution,
    ← integral_sub (positiveConvolution_integrable_at hf hl hbound x)
      (positiveConvolution_integrable_at hf hl hbound y), ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ s, ((C * (60/l^2)) * |x-y|) * lineEnvelope x l 1 s :=
      norm_integral_le_of_norm_le hm (Filter.Eventually.of_forall hp)
    _ = ((C * (60/l^2)) * |x-y|) * (Real.pi*l) := by
      rw [integral_const_mul, integral_lineEnvelope_one x l hl]
    _ = _ := by field_simp

theorem positiveConvolution_continuous {f : ℝ → ℝ} (hf : Measurable f)
    {C l : ℝ} (hC : 0 ≤ C) (hl : 0 < l) (hbound : ∀ s, ‖f s‖ ≤ C) :
    Continuous (positiveConvolution l f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  let A := (60 * Real.pi * C) / l
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨min l (ε/(A+1)), lt_min hl (div_pos hε (by positivity)), ?_⟩
  intro y hy
  have hdist : |y-x| < min l (ε/(A+1)) := by simpa only [Real.dist_eq] using hy
  have hsmall : |y-x| ≤ 2*l := by linarith [lt_of_lt_of_le hdist (min_le_left _ _)]
  have h := positiveConvolution_oscillation hf hC hl hbound y x hsmall
  have he : (A+1)*|y-x| < ε := by
    have h := (lt_div_iff₀ (by positivity : 0 < A+1)).mp
      (lt_of_lt_of_le hdist (min_le_right _ _))
    nlinarith
  rw [Real.dist_eq]
  change |positiveConvolution l f y - positiveConvolution l f x| < ε
  change _ ≤ A*|y-x| at h
  nlinarith [abs_nonneg (y-x)]

end LipschitzHilbert

end

end OAI
