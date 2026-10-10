import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! From almost-everywhere line estimates to planar estimates, including
the area-preserving coordinates of a fixed reference slope. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- For a nonnegative measurable integrand, integrable slices and a common
integrable bound on their integrals prove the full product estimate. -/
theorem integral_le_of_slices (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (f g : α × β → ℝ) {C : ℝ}
    (hfmeas : AEStronglyMeasurable f (μ.prod ν)) (hf0 : ∀ z, 0 ≤ f z)
    (hg : Integrable g (μ.prod ν))
    (hfslice : ∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ)
    (hbound : ∀ᵐ y ∂ν, (∫ x, f (x, y) ∂μ) ≤ C * ∫ x, g (x, y) ∂μ) :
    Integrable f (μ.prod ν) ∧
      (∫ z, f z ∂μ.prod ν) ≤ C * ∫ z, g z ∂μ.prod ν := by
  have hi : Integrable (fun y => ∫ x, f (x, y) ∂μ) ν :=
    (hg.integral_prod_right.const_mul C).mono'
      hfmeas.prod_swap.integral_prod_right' (by
        filter_upwards [hbound] with y hy
        have hnonneg : 0 ≤ ∫ x, f (x, y) ∂μ := integral_nonneg fun x => hf0 (x, y)
        simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hy)
  have hinorm : Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂μ) ν := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hi
  have hf : Integrable f (μ.prod ν) := (integrable_prod_iff' hfmeas).2 ⟨hfslice, hinorm⟩
  refine ⟨hf, ?_⟩
  rw [integral_prod_symm f hf, integral_prod_symm g hg, ← integral_const_mul]
  exact integral_mono_ae hi (hg.integral_prod_right.const_mul C) hbound

/-- The coordinate map `(x,y) ↦ (x,y+s*x)`, with its explicit inverse. -/
def slopeShear (s : ℝ) : ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun z := (z.1, z.2 + s * z.1)
  invFun z := (z.1, z.2 - s * z.1)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  measurable_toFun := measurable_fst.prodMk (measurable_snd.add (measurable_const.mul measurable_fst))
  measurable_invFun := measurable_fst.prodMk (measurable_snd.sub (measurable_const.mul measurable_fst))

theorem slopeShear_measurePreserving (s : ℝ) :
    MeasurePreserving (slopeShear s) (volume.prod volume) (volume.prod volume) := by
  change MeasurePreserving (fun z : ℝ × ℝ => (z.1, z.2 + s * z.1)) _ _
  exact (MeasurePreserving.id volume).skew_product
    (measurable_snd.add (measurable_const.mul measurable_fst))
    (Filter.Eventually.of_forall fun x => map_add_right_eq_self volume (s * x))

theorem integral_slopeShear (s : ℝ) (f : ℝ × ℝ → ℝ) :
    (∫ z, f (slopeShear s z) ∂volume.prod volume) = ∫ z, f z ∂volume.prod volume :=
  (slopeShear_measurePreserving s).integral_comp (slopeShear s).measurableEmbedding f

/-- The slice argument applies in the reference-line coordinates without
requiring a jointly measurable family of auxiliary prediction functions. -/
theorem integral_le_of_slope_slices (s : ℝ) (f g : ℝ × ℝ → ℝ) {C : ℝ}
    (hfmeas : AEStronglyMeasurable f (volume.prod volume)) (hf0 : ∀ z, 0 ≤ f z)
    (hg : Integrable g (volume.prod volume))
    (hfslice : ∀ᵐ y ∂volume, Integrable (fun x => f (x, y + s * x)) volume)
    (hbound : ∀ᵐ y ∂volume,
      (∫ x, f (x, y + s * x)) ≤ C * ∫ x, g (x, y + s * x)) :
    Integrable f (volume.prod volume) ∧
      (∫ z, f z ∂volume.prod volume) ≤ C * ∫ z, g z ∂volume.prod volume := by
  have hpres := slopeShear_measurePreserving s
  obtain ⟨hfi, hle⟩ := integral_le_of_slices volume volume
    (f ∘ slopeShear s) (g ∘ slopeShear s)
    (hfmeas.comp_measurePreserving hpres) (fun z => hf0 _)
    (hpres.integrable_comp_of_integrable hg) hfslice hbound
  refine ⟨(hpres.integrable_comp hfmeas).1 hfi, ?_⟩
  simpa only [Function.comp_apply, integral_slopeShear] using hle

end LipschitzHilbert

end

end OAI
