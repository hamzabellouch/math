import OAI.Analysis.LipschitzHilbert.Fourier.VerticalConvolutionL1
import OAI.Analysis.LipschitzHilbert.Estimates.WeightedCauchySchwarz

namespace OAI

/-! The vertical convolution energy bound for measurable L2 functions. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalConvolution_energy_joint_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) :
    Integrable (fun p : ℝ×(ℝ×ℝ) => ‖K p.1‖*‖f (p.2.1,p.2.2-p.1)‖^2)
      (volume.prod planeMeasure) := by
  have hm : Measurable (fun p : ℝ×(ℝ×ℝ) => ‖K p.1‖*‖f (p.2.1,p.2.2-p.1)‖^2) := by
    exact (hKm.comp measurable_fst).norm.mul ((hfm.comp (by fun_prop)).norm.pow_const 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((verticalTranslation_measurePreserving t).integrable_comp_of_integrable
        (hf.integrable_norm_pow (by decide : 2≠0))).const_mul ‖K t‖
  · have heq (t : ℝ) : (∫ z, ‖‖K t‖*‖f (z.1,z.2-t)‖^2‖ ∂planeMeasure)=
        ‖K t‖*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
      simp only [norm_mul,Real.norm_of_nonneg (norm_nonneg (K t)),
        Real.norm_of_nonneg (sq_nonneg _)]
      rw [integral_const_mul,integral_verticalTranslation t (fun z => ‖f z‖^2)]
    simp_rw [heq]
    exact hK.norm.mul_const _

theorem verticalConvolution_pointwise_energy (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (z : ℝ×ℝ)
    (he : Integrable (fun t => ‖K t‖*‖f (z.1,z.2-t)‖^2)) :
    ‖verticalConvolution K f z‖^2≤
      (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z.1,z.2-t)‖^2) := by
  obtain ⟨hi,hsq⟩ := weighted_integral_cauchySchwarz volume
    (fun t => ‖K t‖) (fun t => ‖f (z.1,z.2-t)‖)
    hKm.norm (hfm.norm.comp (by fun_prop)) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hK.norm he
  have hn : ‖verticalConvolution K f z‖≤∫ t, ‖K t‖*‖f (z.1,z.2-t)‖ := by
    exact norm_integral_le_of_norm_le hi
      (Filter.Eventually.of_forall (fun t => le_of_eq (norm_mul _ _)))
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hsq

theorem verticalConvolution_energy_bound (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) :
    MemLp (verticalConvolution K f) 2 planeMeasure ∧
      (∫ z, ‖verticalConvolution K f z‖^2 ∂planeMeasure)≤
        (∫ t, ‖K t‖)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
  have hi := verticalConvolution_energy_joint_integrable K hK hKm f hfm hf
  have hm := verticalConvolution_measurable K hKm f hfm
  have hp : ∀ᵐ z ∂planeMeasure, ‖verticalConvolution K f z‖^2≤
      (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z.1,z.2-t)‖^2) := by
    filter_upwards [hi.prod_left_ae] with z hz
    exact verticalConvolution_pointwise_energy K hK hKm f hfm z hz
  have hdom : Integrable (fun z => (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z.1,z.2-t)‖^2))
      planeMeasure := hi.integral_prod_right.const_mul _
  have he : Integrable (fun z => ‖verticalConvolution K f z‖^2) planeMeasure := by
    apply hdom.mono' (hm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hp] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2 he,?_⟩
  calc
    _ ≤ ∫ z, (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z.1,z.2-t)‖^2) ∂planeMeasure :=
      integral_mono_ae he hdom hp
    _ = (∫ t, ‖K t‖)^2*(∫ z, ‖f z‖^2 ∂planeMeasure) := by
      rw [integral_const_mul]
      have hs := integral_integral_swap
        (f:=fun (z : ℝ×ℝ) (t : ℝ) => ‖K t‖*‖f (z.1,z.2-t)‖^2) hi.swap
      rw [hs]
      simp_rw [integral_const_mul,integral_verticalTranslation _ (fun z => ‖f z‖^2)]
      rw [integral_mul_const]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
