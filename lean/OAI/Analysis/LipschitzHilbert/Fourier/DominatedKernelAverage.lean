import OAI.Analysis.LipschitzHilbert.Fourier.KernelAverageEnergy

namespace OAI

/-! A time kernel may depend measurably on the output point. An integrable
scalar majorant still gives the same elementary L2 averaging bound. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem dominatedKernelAverage_energy (A : ℝ×(ℝ×ℝ) → ℂ) (hAm : Measurable A)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw : Integrable w) (hw0 : ∀ t, 0≤w t)
    (hA : ∀ p, ‖A p‖≤w p.1) (F : ℝ×(ℝ×ℝ) → ℂ) (hFm : Measurable F)
    (B : ℝ) (hF : ∀ t, MemLp (fun z => F (t,z)) 2 planeMeasure)
    (henergy : ∀ t, (∫ z, ‖F (t,z)‖^2 ∂planeMeasure)≤B) :
    MemLp (fun z => ∫ t, A (t,z)*F (t,z)) 2 planeMeasure ∧
      (∫ z, ‖∫ t, A (t,z)*F (t,z)‖^2 ∂planeMeasure)≤(∫ t, w t)^2*B := by
  let H := fun p : ℝ×(ℝ×ℝ) => w p.1*‖F p‖^2
  have hHm : Measurable H := (hwm.comp measurable_fst).mul (hFm.norm.pow_const 2)
  have hH0 (p) : 0≤H p := mul_nonneg (hw0 _) (sq_nonneg _)
  have hi : Integrable H (volume.prod planeMeasure) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun t =>
        ((hF t).integrable_norm_pow (by decide : 2≠0)).const_mul (w t)
    · apply (hw.mul_const B).mono'
        hHm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with t
      rw [Real.norm_of_nonneg (integral_nonneg fun z => norm_nonneg (H (t,z)))]
      simp only [Real.norm_of_nonneg (hH0 _)]
      change (∫ z, w t*‖F (t,z)‖^2 ∂planeMeasure)≤w t*B
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (henergy t) (hw0 t)
  have hm : Measurable (fun z => ∫ t, A (t,z)*F (t,z)) :=
    (hAm.mul hFm).stronglyMeasurable.prod_swap.integral_prod_right'.measurable
  have hp : ∀ᵐ z ∂planeMeasure, ‖∫ t, A (t,z)*F (t,z)‖^2≤
      (∫ t, w t)*(∫ t, H (t,z)) := by
    filter_upwards [hi.prod_left_ae] with z hz
    obtain ⟨hprod,hcs⟩ := weighted_integral_cauchySchwarz volume w
      (fun t => ‖F (t,z)‖) hwm (hFm.norm.comp (by fun_prop))
      hw0 (fun _ => norm_nonneg _) hw hz
    have hn : ‖∫ t, A (t,z)*F (t,z)‖≤∫ t, w t*‖F (t,z)‖ :=
      norm_integral_le_of_norm_le hprod (Filter.Eventually.of_forall fun t => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hA (t,z)) (norm_nonneg _))
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs
  have hdom := hi.integral_prod_right.const_mul (∫ t, w t)
  have he : Integrable (fun z => ‖∫ t, A (t,z)*F (t,z)‖^2) planeMeasure := by
    apply hdom.mono' (hm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hp] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2 he,?_⟩
  have htotal : (∫ t, ∫ z, H (t,z) ∂planeMeasure)≤(∫ t, w t)*B := by
    rw [←integral_mul_const]
    apply integral_mono hi.integral_prod_left (hw.mul_const B)
    intro t
    change (∫ z, w t*‖F (t,z)‖^2 ∂planeMeasure)≤_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (henergy t) (hw0 t)
  calc
    _ ≤ ∫ z, (∫ t, w t)*(∫ t, H (t,z)) ∂planeMeasure :=
      integral_mono_ae he hdom hp
    _ = (∫ t, w t)*(∫ t, ∫ z, H (t,z) ∂planeMeasure) := by
      rw [integral_const_mul]
      exact congrArg (fun a => (∫ t, w t)*a)
        (integral_integral_swap (f:=fun (z : ℝ×ℝ) (t : ℝ) => H (t,z)) hi.swap)
    _ ≤ (∫ t, w t)*((∫ t, w t)*B) :=
      mul_le_mul_of_nonneg_left htotal (integral_nonneg hw0)
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
