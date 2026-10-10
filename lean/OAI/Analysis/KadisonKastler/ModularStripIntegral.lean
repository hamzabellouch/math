import OAI.Analysis.KadisonKastler.ModularStripBounds
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! # Integrating the bounded modular strip kernel -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (r : X → ℝ)
  (hr : Measurable r) (f : X → ℂ) (hf : Integrable f μ)
  (hint : ∀ᵐ s ∂μ, 0 < r s ∧ r s < 1)

def modularStripIntegral (z : ℂ) : ℂ := ∫ s, f s * modularStripKernel z (r s) ∂μ

include hr in
theorem modularStripKernel_comp_measurable (z : ℂ) :
    Measurable (fun s => modularStripKernel z (r s)) := by
  unfold modularStripKernel
  exact (Complex.continuous_ofReal.measurable.comp hr).mul
    (Complex.continuous_exp.measurable.comp (measurable_const.mul
      (Complex.continuous_ofReal.measurable.comp (resolventLogFrequency_measurable.comp hr))))

include hr hf in
theorem modularStripIntegrand_measurable (z : ℂ) :
    AEStronglyMeasurable (fun s => f s * modularStripKernel z (r s)) μ :=
  hf.aestronglyMeasurable.mul (modularStripKernel_comp_measurable r hr z).aestronglyMeasurable

include hint in
theorem modularStripIntegrand_bound {z : ℂ} (hz : 0 ≤ z.im ∧ z.im ≤ 1) :
    ∀ᵐ s ∂μ, ‖f s * modularStripKernel z (r s)‖ ≤ ‖f s‖ := by
  filter_upwards [hint] with s hs
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (modularStripKernel_norm_le_one hs.1 hs.2 hz.1 hz.2)
    (norm_nonneg _)).trans_eq (mul_one _)

include hr hf hint in
theorem modularStripIntegral_continuousOn :
    ContinuousOn (modularStripIntegral μ r f) {z : ℂ | 0 ≤ z.im ∧ z.im ≤ 1} := by
  apply continuousOn_of_dominated
    (fun z _ => modularStripIntegrand_measurable μ r hr f hf z)
    (fun _ hz => modularStripIntegrand_bound μ r f hint hz) hf.norm
  filter_upwards [] with s
  exact (continuous_const.mul (modularStripKernel_differentiable (r s)).continuous).continuousOn

include hf hint in
theorem modularStripIntegral_bound {z : ℂ} (hz : 0 ≤ z.im ∧ z.im ≤ 1) :
    ‖modularStripIntegral μ r f z‖ ≤ ∫ s, ‖f s‖ ∂μ :=
  norm_integral_le_of_norm_le hf.norm (modularStripIntegrand_bound μ r f hint hz)

include hr hf hint in
theorem modularStripIntegral_differentiableOn :
    DifferentiableOn ℂ (modularStripIntegral μ r f) {z : ℂ | 0 < z.im ∧ z.im < 1} := by
  intro z hz
  change 0 < z.im ∧ z.im < 1 at hz
  let δ : ℝ := min z.im (1 - z.im) / 2
  have hδ : 0 < δ := div_pos (lt_min hz.1 (sub_pos.mpr hz.2)) (by norm_num)
  have hδ₀ : δ < z.im := by
    have h := min_le_left z.im (1 - z.im)
    dsimp [δ]
    linarith [hz.1]
  have hδ₁ : z.im < 1 - δ := by
    have h := min_le_right z.im (1 - z.im)
    dsimp [δ]
    linarith [hz.2]
  let S : Set ℂ := {w | δ < w.im ∧ w.im < 1 - δ}
  have hS : S ∈ 𝓝 z :=
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)).mem_nhds ⟨hδ₀, hδ₁⟩
  let F' : ℂ → X → ℂ := fun w s =>
    f s * ((-Complex.I * (resolventLogFrequency (r s) : ℂ)) * modularStripKernel w (r s))
  have hm (w : ℂ) : AEStronglyMeasurable (F' w) μ := by
    exact hf.aestronglyMeasurable.mul
      ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp
        (resolventLogFrequency_measurable.comp hr))).mul
        (modularStripKernel_comp_measurable r hr w)).aestronglyMeasurable
  have hI : Integrable (fun s => f s * modularStripKernel z (r s)) μ :=
    hf.norm.mono' (modularStripIntegrand_measurable μ r hr f hf z)
      (modularStripIntegrand_bound μ r f hint ⟨hz.1.le, hz.2.le⟩)
  have hB : ∀ᵐ s ∂μ, ∀ w ∈ S, ‖F' w s‖ ≤ ‖f s‖ * (1 / δ) := by
    filter_upwards [hint] with s hs w hw
    exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left
      (modularStripKernel_deriv_bound hs.1 hs.2 hδ hw.1.le hw.2.le) (norm_nonneg _))
  have hD : ∀ᵐ s ∂μ, ∀ w ∈ S,
      HasDerivAt (fun w => f s * modularStripKernel w (r s)) (F' w s) w := by
    filter_upwards [] with s w _
    exact (modularStripKernel_hasDerivAt (r s) w).const_mul (f s)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Eventually.of_forall fun w => modularStripIntegrand_measurable μ r hr f hf w) hI
    (hm z) hB (hf.norm.mul_const (1 / δ)) hD).2.differentiableAt.differentiableWithinAt

end

end KadisonKastler

end OAI
