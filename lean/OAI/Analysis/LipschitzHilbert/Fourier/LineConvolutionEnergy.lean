import OAI.Analysis.LipschitzHilbert.Estimates.WeightedCauchySchwarz
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! The one-dimensional convolution energy bound for measurable L2 functions. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def lineConvolution (K f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t, K t*f (x-t)

theorem lineTranslation_measurePreserving (t : ℝ) :
    MeasurePreserving (fun x : ℝ => x-t) volume volume :=
  measurePreserving_sub_right volume t

theorem lineConvolution_measurable (K : ℝ → ℂ) (hK : Measurable K)
    (f : ℝ → ℂ) (hf : Measurable f) : Measurable (lineConvolution K f) := by
  have hm : Measurable (fun p : ℝ×ℝ => K p.2*f (p.1-p.2)) :=
    (hK.comp measurable_snd).mul (hf.comp (by fun_prop))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable


theorem lineConvolution_energy_joint_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 volume) :
    Integrable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^2)
      (volume.prod volume) := by
  have hm : Measurable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^2) := by
    exact (hKm.comp measurable_fst).norm.mul ((hfm.comp (by fun_prop)).norm.pow_const 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((lineTranslation_measurePreserving t).integrable_comp_of_integrable
        (hf.integrable_norm_pow (by decide : 2≠0))).const_mul ‖K t‖
  · have heq (t : ℝ) : (∫ z, ‖‖K t‖*‖f (z-t)‖^2‖ ∂volume)=
        ‖K t‖*(∫ z, ‖f z‖^2 ∂volume) := by
      simp only [norm_mul,Real.norm_of_nonneg (norm_nonneg (K t)),
        Real.norm_of_nonneg (sq_nonneg _)]
      rw [integral_const_mul,integral_sub_right_eq_self (fun z => ‖f z‖^2) t]
    simp_rw [heq]
    exact hK.norm.mul_const _

theorem lineConvolution_pointwise_energy (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ → ℂ) (hfm : Measurable f) (z : ℝ)
    (he : Integrable (fun t => ‖K t‖*‖f (z-t)‖^2)) :
    ‖lineConvolution K f z‖^2≤
      (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z-t)‖^2) := by
  obtain ⟨hi,hsq⟩ := weighted_integral_cauchySchwarz volume
    (fun t => ‖K t‖) (fun t => ‖f (z-t)‖)
    hKm.norm (hfm.norm.comp (by fun_prop)) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hK.norm he
  have hn : ‖lineConvolution K f z‖≤∫ t, ‖K t‖*‖f (z-t)‖ := by
    exact norm_integral_le_of_norm_le hi
      (Filter.Eventually.of_forall (fun t => le_of_eq (norm_mul _ _)))
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hsq

theorem lineConvolution_energy_bound (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 volume) :
    MemLp (lineConvolution K f) 2 volume ∧
      (∫ z, ‖lineConvolution K f z‖^2 ∂volume)≤
        (∫ t, ‖K t‖)^2*(∫ z, ‖f z‖^2 ∂volume) := by
  have hi := lineConvolution_energy_joint_integrable K hK hKm f hfm hf
  have hm := lineConvolution_measurable K hKm f hfm
  have hp : ∀ᵐ z ∂volume, ‖lineConvolution K f z‖^2≤
      (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z-t)‖^2) := by
    filter_upwards [hi.prod_left_ae] with z hz
    exact lineConvolution_pointwise_energy K hK hKm f hfm z hz
  have hdom : Integrable (fun z => (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z-t)‖^2))
      volume := hi.integral_prod_right.const_mul _
  have he : Integrable (fun z => ‖lineConvolution K f z‖^2) volume := by
    apply hdom.mono' (hm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hp] with z hz
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hz
  refine ⟨(memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2 he,?_⟩
  calc
    _ ≤ ∫ z, (∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (z-t)‖^2) ∂volume :=
      integral_mono_ae he hdom hp
    _ = (∫ t, ‖K t‖)^2*(∫ z, ‖f z‖^2 ∂volume) := by
      rw [integral_const_mul]
      have hs := integral_integral_swap
        (f:=fun (z : ℝ) (t : ℝ) => ‖K t‖*‖f (z-t)‖^2) hi.swap
      rw [hs]
      simp_rw [integral_const_mul,integral_sub_right_eq_self (fun z => ‖f z‖^2) _]
      rw [integral_mul_const]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
