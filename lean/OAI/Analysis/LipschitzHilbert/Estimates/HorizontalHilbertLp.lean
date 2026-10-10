import OAI.Analysis.LipschitzHilbert.Estimates.PublishedHilbertInput
import OAI.Analysis.LipschitzHilbert.Fourier.PlanarSchwartzSlice
import OAI.Analysis.LipschitzHilbert.Estimates.SharpTimeMoment

namespace OAI

/-! Fubini transfers the precisely stated one-dimensional Hilbert input
to the horizontal remainder on the actual plane. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def horizontalTruncatedHilbert (r R : ℝ) (f : (ℝ×ℝ) → ℂ) (z : ℝ×ℝ) : ℂ :=
  slopeKernelOperator (sharpTimeKernel r R) (fun _ => 0) f z

theorem horizontalTruncatedHilbert_slice (r R : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (x y : ℝ) :
    horizontalTruncatedHilbert r R f (x,y)=
      oneDimensionalTruncatedHilbert r R (planarSchwartzSlice f y 0) x := by
  simp only [horizontalTruncatedHilbert,slopeKernelOperator,oneDimensionalTruncatedHilbert,
    planarSchwartzSlice_apply,mul_zero,sub_zero,zero_mul,add_zero]

theorem horizontalTruncatedHilbert_measurable (r R : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Measurable (horizontalTruncatedHilbert r R f) := by
  have hm : Measurable (fun p : (ℝ×ℝ)×ℝ =>
      sharpTimeKernel r R p.2*f (p.1.1-p.2,p.1.2)) :=
    ((sharpTimeKernel_measurable r R).comp measurable_snd).mul
      (f.continuous.measurable.comp (by fun_prop))
  have hmi : Measurable (fun z : ℝ×ℝ => ∫ t : ℝ,
      sharpTimeKernel r R t*f (z.1-t,z.2)) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  change Measurable (fun z => horizontalTruncatedHilbert r R f z)
  simpa only [horizontalTruncatedHilbert,slopeKernelOperator,mul_zero,sub_zero] using hmi

theorem horizontalHilbert_power_bound (hH : HorizontalHilbertInput) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, p=3/2 ∨ p=4 →
      ∀ r R : ℝ, 0<r → r≤R → ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
        Integrable (fun z => ‖horizontalTruncatedHilbert r R f z‖^p) planeMeasure ∧
        (∫ z, ‖horizontalTruncatedHilbert r R f z‖^p ∂planeMeasure)≤
          C^p*(∫ z, ‖f z‖^p ∂planeMeasure) := by
  obtain ⟨C,hC,hbound⟩ := hH
  refine ⟨C,hC,?_⟩
  intro p hp r R hr hrR f
  have hp0 : 0<p := by rcases hp with h | h <;> rw [h] <;> norm_num
  let H := fun z : ℝ×ℝ => ‖horizontalTruncatedHilbert r R f (z.2,z.1)‖^p
  have hHm : Measurable H :=
    ((horizontalTruncatedHilbert_measurable r R f).comp measurable_swap).norm.pow_const p
  have hH0 (z) : 0≤H z := Real.rpow_nonneg (norm_nonneg _) _
  have hf : Integrable (fun z => ‖f z‖^p) planeMeasure := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      (f.memLp (ENNReal.ofReal p) planeMeasure).integrable_norm_rpow
        (by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hp0) (by simp)
  have hslice (y : ℝ) : Integrable (fun x => H (y,x)) ∧
      (∫ x, H (y,x))≤C^p*(∫ x, ‖f (x,y)‖^p) := by
    simpa only [H,horizontalTruncatedHilbert_slice,planarSchwartzSlice_apply,
      zero_mul,add_zero] using hbound p hp r R hr hrR (planarSchwartzSlice f y 0)
  have hHi : Integrable H (volume.prod volume) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun y => (hslice y).1
    · apply (hf.swap.integral_prod_left.const_mul (C^p)).mono'
        hHm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with y
      simp only [Real.norm_of_nonneg (hH0 _)]
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => hH0 _)]
      exact (hslice y).2
  have hmain : (∫ z, H z ∂volume.prod volume)≤C^p*(∫ z, ‖f z‖^p ∂planeMeasure) := by
    rw [integral_prod _ hHi]
    calc
      _ ≤ ∫ y, C^p*(∫ x, ‖f (x,y)‖^p) :=
        integral_mono hHi.integral_prod_left (hf.swap.integral_prod_left.const_mul (C^p))
          (fun y => (hslice y).2)
      _ = C^p*(∫ z, ‖f z‖^p ∂planeMeasure) := by
        rw [integral_const_mul]
        congr 1
        exact (integral_prod_symm _ hf).symm
  have hi : Integrable (fun z => ‖horizontalTruncatedHilbert r R f z‖^p) planeMeasure := by
    simpa only [H,Function.comp_def,Prod.swap_prod_mk,Prod.fst_swap,Prod.snd_swap,Prod.mk.eta] using hHi.swap
  refine ⟨hi,?_⟩
  have heq : (∫ z, H z ∂volume.prod volume)=
      ∫ z, ‖horizontalTruncatedHilbert r R f z‖^p ∂planeMeasure := by
    simpa only [H,Prod.swap_prod_mk,Prod.fst_swap,Prod.snd_swap,Prod.mk.eta] using
      (MeasureTheory.integral_prod_swap (μ := volume) (ν := volume) H).symm
  exact heq ▸ hmain

end LipschitzHilbert.PacketRepresentation

end

end OAI
