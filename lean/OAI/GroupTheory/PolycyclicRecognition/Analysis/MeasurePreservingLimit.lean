import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

/-! # Passing coordinate measure invariance to a limiting group law -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Fatou's lemma on open sets: a pointwise limit of measure preserving maps
cannot increase an outer regular target measure. -/
theorem map_le_of_measurePreserving_limit
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [ν.OuterRegular]
    (g : X → Y) (hg : Measurable g) (gn : ℕ → X → Y)
    (hgn : ∀ n, MeasurePreserving (gn n) μ ν)
    (hlim : ∀ x, Tendsto (fun n => gn n x) atTop (𝓝 (g x))) :
    Measure.map g μ ≤ ν := by
  have hopen (U : Set Y) (hU : IsOpen U) : μ (g ⁻¹' U) ≤ ν U := by
    let χ : Y → ℝ≥0∞ := U.indicator (fun _ => 1)
    have hχ : Measurable χ := measurable_const.indicator hU.measurableSet
    have hpoint (x : X) : χ (g x) ≤ liminf (fun n => χ (gn n x)) atTop := by
      by_cases hx : g x ∈ U
      · refine le_liminf_of_le (by isBoundedDefault) ?_
        filter_upwards [(hlim x).eventually (hU.mem_nhds hx)] with n hn
        simp only [χ, indicator_of_mem hx, indicator_of_mem hn]
        exact le_rfl
      · simp only [χ, indicator_of_notMem hx, zero_le]
    calc
      μ (g ⁻¹' U) = ∫⁻ x, χ (g x) ∂μ := by
        simp only [χ, ← indicator_comp_right, Function.comp_def]
        exact (lintegral_indicator_one (hg hU.measurableSet)).symm
      _ ≤ ∫⁻ x, liminf (fun n => χ (gn n x)) atTop ∂μ := lintegral_mono hpoint
      _ ≤ liminf (fun n => ∫⁻ x, χ (gn n x) ∂μ) atTop :=
        lintegral_liminf_le (fun n => hχ.comp (hgn n).measurable)
      _ = ν U := by
        simp only [(hgn _).lintegral_comp hχ, liminf_const]
        exact lintegral_indicator_one hU.measurableSet
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hg hA, A.measure_eq_iInf_isOpen ν]
  exact le_iInf fun U => le_iInf fun hAU => le_iInf fun hU =>
    (measure_mono (preimage_mono hAU)).trans (hopen U hU)

/-- For homeomorphisms, applying the preceding estimate to both the map and
its inverse proves exact measure preservation of the pointwise limit. -/
theorem measurePreserving_homeomorph_limit
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.OuterRegular] (e : X ≃ₜ X) (en : ℕ → X ≃ₜ X)
    (hen : ∀ n, MeasurePreserving (en n) μ μ)
    (hlim : ∀ x, Tendsto (fun n => en n x) atTop (𝓝 (e x)))
    (hlimInv : ∀ x, Tendsto (fun n => (en n).symm x) atTop (𝓝 (e.symm x))) :
    MeasurePreserving e μ μ := by
  have hforward := map_le_of_measurePreserving_limit μ μ e e.continuous.measurable
    (fun n => en n) hen hlim
  have hbackward := map_le_of_measurePreserving_limit μ μ e.symm
    e.symm.continuous.measurable (fun n => (en n).symm)
    (fun n => (hen n).symm (en n).toMeasurableEquiv) hlimInv
  refine ⟨e.continuous.measurable, le_antisymm hforward ?_⟩
  have h := Measure.map_mono hbackward e.continuous.measurable
  simpa only [Measure.map_map e.continuous.measurable e.symm.continuous.measurable,
    show (e : X → X) ∘ e.symm = id from funext e.apply_symm_apply,
    Measure.map_id] using h

end PolycyclicRecognition

end

end OAI
