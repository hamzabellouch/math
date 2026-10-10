import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem masked_pushforward_decomposition {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (f : α → β) (hf : Measurable f) (w m : α → ℝ≥0∞)
    (hw : Measurable w) (hm : Measurable m) (hm1 : ∀ x, m x ≤ 1) :
    (μ.withDensity w).map f =
      (μ.withDensity (fun x => w x*m x)).map f +
      (μ.withDensity (fun x => w x*(1-m x))).map f := by
  have hd : μ.withDensity w =
      μ.withDensity (fun x => w x*m x) + μ.withDensity (fun x => w x*(1-m x)) := by
    rw [← withDensity_add_left (μ := μ)
      (show Measurable (fun x => w x*m x) from hw.mul hm)
      (fun x => w x*(1-m x))]
    congr 1
    funext x
    dsimp
    rw [← mul_add, add_tsub_cancel_of_le (hm1 x), mul_one]
  rw [hd, Measure.map_add _ _ hf]

theorem masked_pushforward_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (f : α → β) (hf : Measurable f) (w m : α → ℝ≥0∞)
    (hw : Measurable w) (hm : Measurable m) (hm1 : ∀ x, m x ≤ 1) :
    (μ.withDensity (fun x => w x*m x)).map f ≤ (μ.withDensity w).map f := by
  rw [masked_pushforward_decomposition μ f hf w m hw hm hm1]
  apply Measure.le_iff.mpr
  intro s _
  simp only [Measure.add_apply]
  exact le_add_right le_rfl

theorem removed_pushforward_mass_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (f : α → β) (hf : Measurable f) (w m : α → ℝ≥0∞)
    (bad : Set α) (C : ℝ≥0∞)
    (hbound : ∀ᵐ x ∂μ, w x ≤ C)
    (hout : ∀ᵐ x ∂μ, x ∉ bad → m x = 1) :
    (μ.withDensity (fun x => w x*(1-m x))).map f univ ≤ C*μ bad := by
  rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    (∫⁻ x, w x*(1-m x) ∂μ) ≤ ∫⁻ x, bad.indicator (fun _ => C) x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hbound,hout] with x hx houtx
      by_cases hxb : x ∈ bad
      · rw [Set.indicator_of_mem hxb]
        calc
          w x*(1-m x) ≤ w x*1 := mul_le_mul_right tsub_le_self _
          _ ≤ C := by simpa only [mul_one] using hx
      · rw [Set.indicator_of_notMem hxb, houtx hxb, tsub_self, mul_zero]
    _ ≤ C*μ bad := lintegral_indicator_const_le bad C

end PlanarFalconer

end OAI
