import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-! Sectionwise integration of a measurable density on a product measure. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace SLEExactGauge

lemma product_withDensity_lintegral
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y) [SFinite ν]
    (d : X × Y → ℝ≥0∞) (hd : Measurable d)
    (f : X × Y → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂(μ.prod ν).withDensity d) =
      ∫⁻ x, ∫⁻ y, f (x,y) ∂ν.withDensity (fun y => d (x,y)) ∂μ := by
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hf,
    lintegral_prod _ (hd.mul hf).aemeasurable]
  apply lintegral_congr
  intro x
  have hdx : Measurable (fun y => d (x,y)) := hd.comp (measurable_const.prodMk measurable_id)
  have hfx : Measurable (fun y => f (x,y)) := hf.comp (measurable_const.prodMk measurable_id)
  exact (lintegral_withDensity_eq_lintegral_mul ν hdx hfx).symm

end SLEExactGauge

end

end OAI
