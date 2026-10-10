import OAI.Analysis.LipschitzHilbert.Fourier.VerticalConvolutionL2

namespace OAI

/-! An energy bound for a time average of a uniformly bounded family.
This is used with the time-normalized sampling commutator. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem kernelAverage_energy (K : ℝ → ℂ) (hKm : Measurable K)
    (hK : Integrable K) (F : ℝ×(ℝ×ℝ) → ℂ) (hFm : Measurable F)
    (B : ℝ) (_hB : 0≤B) (hF : ∀ t, MemLp (fun z => F (t,z)) 2 planeMeasure)
    (henergy : ∀ t, (∫ z, ‖F (t,z)‖^2 ∂planeMeasure)≤B) :
    MemLp (fun z => ∫ t, K t*F (t,z)) 2 planeMeasure ∧
      (∫ z, ‖∫ t, K t*F (t,z)‖^2 ∂planeMeasure)≤(∫ t, ‖K t‖)^2*B := by
  let H := fun p : ℝ×(ℝ×ℝ) => ‖K p.1‖*‖F p‖^2
  have hHm : Measurable H := (hKm.comp measurable_fst).norm.mul (hFm.norm.pow_const 2)
  have hH0 (p) : 0≤H p := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hi : Integrable H (volume.prod planeMeasure) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun t =>
        ((hF t).integrable_norm_pow (by decide : 2≠0)).const_mul ‖K t‖
    · apply (hK.norm.mul_const B).mono'
        hHm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with t
      change ‖∫ z, ‖H (t,z)‖ ∂planeMeasure‖≤‖K t‖*B
      simp only [Real.norm_of_nonneg (hH0 _)]
      rw [Real.norm_of_nonneg (integral_nonneg (fun z => hH0 (t,z)))]
      change (∫ z, ‖K t‖*‖F (t,z)‖^2 ∂planeMeasure)≤_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (henergy t) (norm_nonneg _)
  have hm : Measurable (fun z => ∫ t, K t*F (t,z)) :=
    ((hKm.comp measurable_fst).mul hFm).stronglyMeasurable.prod_swap.integral_prod_right'.measurable
  have hp : ∀ᵐ z ∂planeMeasure, ‖∫ t, K t*F (t,z)‖^2≤
      (∫ t, ‖K t‖)*(∫ t, H (t,z)) := by
    filter_upwards [hi.prod_left_ae] with z hz
    obtain ⟨hprod,hcs⟩ := weighted_integral_cauchySchwarz volume
      (fun t => ‖K t‖) (fun t => ‖F (t,z)‖) hKm.norm
      (hFm.norm.comp (by fun_prop)) (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) hK.norm hz
    have hn : ‖∫ t, K t*F (t,z)‖≤∫ t, ‖K t‖*‖F (t,z)‖ :=
      norm_integral_le_of_norm_le hprod
        (Filter.Eventually.of_forall fun t => le_of_eq (norm_mul _ _))
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs
  have hdom := hi.integral_prod_right.const_mul (∫ t, ‖K t‖)
  have he : Integrable (fun z => ‖∫ t, K t*F (t,z)‖^2) planeMeasure := by
    apply hdom.mono' (hm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hp] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2 he,?_⟩
  have htotal : (∫ t, ∫ z, H (t,z) ∂planeMeasure)≤(∫ t, ‖K t‖)*B := by
    rw [←integral_mul_const]
    apply integral_mono hi.integral_prod_left (hK.norm.mul_const B)
    intro t
    change (∫ z, ‖K t‖*‖F (t,z)‖^2 ∂planeMeasure)≤_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (henergy t) (norm_nonneg _)
  calc
    _ ≤ ∫ z, (∫ t, ‖K t‖)*(∫ t, H (t,z)) ∂planeMeasure :=
      integral_mono_ae he hdom hp
    _ = (∫ t, ‖K t‖)*(∫ t, ∫ z, H (t,z) ∂planeMeasure) := by
      rw [integral_const_mul]
      exact congrArg (fun a => (∫ t, ‖K t‖)*a)
        (integral_integral_swap (f:=fun (z : ℝ×ℝ) (t : ℝ) => H (t,z)) hi.swap)
    _ ≤ (∫ t, ‖K t‖)*((∫ t, ‖K t‖)*B) :=
      mul_le_mul_of_nonneg_left htotal (integral_nonneg fun _ => norm_nonneg _)
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
