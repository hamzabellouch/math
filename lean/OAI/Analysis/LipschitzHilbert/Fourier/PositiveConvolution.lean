import OAI.Analysis.LipschitzHilbert.Fourier.PositiveLineKernel
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Actual convolution of the positive error source with the horizontal
kernel. Bounded measurable sources need not be globally integrable. -/

noncomputable section
open Set MeasureTheory

namespace LipschitzHilbert

def positiveConvolution (l : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s, lineKernel l (x-s) * f s

theorem lineKernel_continuous (l : ℝ) : Continuous (lineKernel l) :=
  (continuous_iff_continuousAt.mpr (fun x => (lineEnvelope_three_hasDerivAt 0 l x).continuousAt)).const_mul _

theorem lineKernel_sub_comm (l x s : ℝ) : lineKernel l (x-s) = lineKernel l (s-x) := by
  simp only [lineKernel, lineEnvelope, sub_zero, div_pow, sub_sq_comm]

theorem positiveConvolution_integrable_at {f : ℝ → ℝ} (hf : Measurable f)
    {C l : ℝ} (hl : 0 < l) (hbound : ∀ s, ‖f s‖ ≤ C) (x : ℝ) :
    Integrable (fun s => lineKernel l (x-s) * f s) := by
  have hi : Integrable (fun s => lineKernel l (x-s)) := by
    simp_rw [lineKernel_sub_comm l x]
    exact lineKernel_integrable l x hl
  exact hi.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

theorem positiveConvolution_nonneg {f : ℝ → ℝ} {l : ℝ} (hl : 0 < l)
    (hf : ∀ s, 0 ≤ f s) (x : ℝ) : 0 ≤ positiveConvolution l f x :=
  integral_nonneg (fun s => mul_nonneg (lineKernel_nonneg l (x-s) hl) (hf s))

theorem positiveConvolution_le {f : ℝ → ℝ} (hf : Measurable f) {C l : ℝ}
    (hl : 0 < l) (hC : 0 ≤ C) (hbound : ∀ s, ‖f s‖ ≤ C) (x : ℝ) :
    ‖positiveConvolution l f x‖ ≤ C * Real.pi := by
  have hi : Integrable (fun s => lineKernel l (x-s)) := by
    simp_rw [lineKernel_sub_comm l x]
    exact lineKernel_integrable l x hl
  calc
    _ ≤ ∫ s, ‖lineKernel l (x-s) * f s‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s, lineKernel l (x-s) * C := by
      apply integral_mono (positiveConvolution_integrable_at hf hl hbound x).norm (hi.mul_const C)
      intro s
      change ‖lineKernel l (x-s) * f s‖ ≤ lineKernel l (x-s) * C
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (lineKernel_nonneg _ _ hl)]
      exact mul_le_mul_of_nonneg_left (hbound s) (lineKernel_nonneg _ _ hl)
    _ = C * ∫ s, lineKernel l (s-x) := by
      simp_rw [lineKernel_sub_comm l x]
      rw [integral_mul_const, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_lineKernel_le l x hl) hC

theorem positiveConvolution_joint_integrable {f : ℝ → ℝ} (hf : Measurable f)
    {C l r : ℝ} (_hC : 0 ≤ C) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r)
    (hf0 : ∀ s, 0 ≤ f s) (hbound : ∀ s, f s ≤ C) (u : ℝ) :
    Integrable (fun p : ℝ × ℝ => lineKernel l (p.2-p.1) * f p.1)
      (volume.prod (volume.restrict (Icc (u-r) (u+r)))) := by
  let μ := volume.restrict (Icc (u-r) (u+r))
  have hm : Measurable (fun p : ℝ × ℝ => lineKernel l (p.2-p.1) * f p.1) :=
    ((lineKernel_continuous l).measurable.comp (measurable_snd.sub measurable_fst)).mul
      (hf.comp measurable_fst)
  have hpart (s : ℝ) : Integrable (fun x => lineKernel l (x-s) * f s) μ :=
    ((lineKernel_integrable l s hl).mul_const _).restrict
  have hinner (s : ℝ) : (∫ x, ‖lineKernel l (x-s) * f s‖ ∂μ) ≤
      (C * (1024 * Real.pi)) * lineEnvelope u r 2 s := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (lineKernel_nonneg _ _ hl) (hf0 s))]
    rw [integral_mul_const]
    calc
      _ ≤ ((1024 * Real.pi) * lineEnvelope u r 2 s) * f s :=
        mul_le_mul_of_nonneg_right (local_lineKernel_integral l u r s hl hr hlr) (hf0 s)
      _ ≤ ((1024 * Real.pi) * lineEnvelope u r 2 s) * C :=
        mul_le_mul_of_nonneg_left (hbound s)
          (mul_nonneg (by positivity) (lineEnvelope_nonneg _ _ _ _))
      _ = _ := by ring
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall hpart, ?_⟩
  apply ((integrable_lineEnvelope u r hr (by decide : 1 ≤ 2)).const_mul
    (C * (1024 * Real.pi))).mono' hm.aestronglyMeasurable.norm.integral_prod_right'
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact hinner s

theorem positiveConvolution_interval_integrable {f : ℝ → ℝ} (hf : Measurable f)
    {C l r : ℝ} (hC : 0 ≤ C) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r)
    (hf0 : ∀ s, 0 ≤ f s) (hbound : ∀ s, f s ≤ C) (u : ℝ) :
    IntegrableOn (positiveConvolution l f) (Icc (u-r) (u+r)) :=
  (positiveConvolution_joint_integrable hf hC hl hr hlr hf0 hbound u).integral_prod_right

theorem integral_positiveConvolution_interval {f : ℝ → ℝ} (hf : Measurable f)
    {C l r : ℝ} (hC : 0 ≤ C) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r)
    (hf0 : ∀ s, 0 ≤ f s) (hbound : ∀ s, f s ≤ C) (u : ℝ) :
    (∫ x in Icc (u-r) (u+r), positiveConvolution l f x) =
      ∫ s, f s * (∫ x in Icc (u-r) (u+r), lineKernel l (x-s)) := by
  have h := integral_integral_swap (f := fun s x => lineKernel l (x-s) * f s)
    (μ := volume) (ν := volume.restrict (Icc (u-r) (u+r)))
    (positiveConvolution_joint_integrable hf hC hl hr hlr hf0 hbound u)
  unfold positiveConvolution
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [integral_mul_const, mul_comm]

end LipschitzHilbert

end

end OAI
