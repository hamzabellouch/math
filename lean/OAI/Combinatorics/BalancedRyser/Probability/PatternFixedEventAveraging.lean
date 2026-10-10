import OAI.Combinatorics.BalancedRyser.Probability.PatternIntegrability
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentModel

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Balanced.PatternModel

universe u

theorem mem_fixed_event_iff (P : PatternModel.{u}) (K : Finset P.Color)
    (S : Set P.Sample)
    (hS : ∀ x y, (∀ c ∈ K, x c = y c) → (x ∈ S ↔ y ∈ S))
    (x ω : P.Sample) : P.fixCoordinates K x ω ∈ S ↔ x ∈ S := by
  apply hS
  intro c hc
  simp [fixCoordinates, hc]

theorem measure_inter_le_of_fixed_measure_le
    (P : PatternModel.{u}) (K : Finset P.Color) (S E : Set P.Sample)
    (hS : MeasurableSet S) (hE : MeasurableSet E)
    (hdepends : ∀ x y, (∀ c ∈ K, x c = y c) → (x ∈ S ↔ y ∈ S))
    (C : ℝ≥0∞)
    (hbound : ∀ x ∈ S, P.measure ((P.fixCoordinates K x) ⁻¹' E) ≤ C) :
    P.measure (S ∩ E) ≤ C * P.measure S := by
  classical
  have hf : Measurable ((S ∩ E).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (hS.inter hE)
  have hg : Measurable (S.indicator (fun _ => C)) :=
    measurable_const.indicator hS
  have h := lintegral_le_of_lmarginal_le (μ := P.law) (Finset.univ \ K) hf hg ?_
  · simpa only [lintegral_indicator_const (hS.inter hE),
      lintegral_indicator_const hS, one_mul, measure] using h
  intro x
  rw [← P.lintegral_fixCoordinates_eq_lmarginal K x _ hf,
    ← P.lintegral_fixCoordinates_eq_lmarginal K x _ hg]
  have hmem (ω : P.Sample) := P.mem_fixed_event_iff K S hdepends x ω
  by_cases hx : x ∈ S
  · have hleft :
        (fun ω => (S ∩ E).indicator (fun _ => (1 : ℝ≥0∞))
          (P.fixCoordinates K x ω)) =
        ((P.fixCoordinates K x) ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_preimage,
        (hmem ω).mpr hx, true_and]
    have hright :
        (fun ω => S.indicator (fun _ => C) (P.fixCoordinates K x ω)) = fun _ => C := by
      funext ω
      simp only [Set.indicator_of_mem ((hmem ω).mpr hx)]
    rw [hleft, hright, lintegral_indicator_const (hE.preimage (P.measurable_fixCoordinates K x))]
    simpa using hbound x hx
  · have hout (ω : P.Sample) : P.fixCoordinates K x ω ∉ S :=
      fun hω => hx ((hmem ω).mp hω)
    simp [Set.indicator, hout]

theorem measureReal_inter_le_of_fixed_measureReal_le
    (P : PatternModel.{u}) (K : Finset P.Color) (S E : Set P.Sample)
    (hS : MeasurableSet S) (hE : MeasurableSet E)
    (hdepends : ∀ x y, (∀ c ∈ K, x c = y c) → (x ∈ S ↔ y ∈ S))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ S, P.measure.real ((P.fixCoordinates K x) ⁻¹' E) ≤ C) :
    P.measure.real (S ∩ E) ≤ C * P.measure.real S := by
  have h := P.measure_inter_le_of_fixed_measure_le K S E hS hE hdepends
    (ENNReal.ofReal C) (by
      intro x hx
      have hb := ENNReal.ofReal_le_ofReal (hbound x hx)
      rwa [ofReal_measureReal (by finiteness)] at hb)
  have hr := ENNReal.toReal_mono (by finiteness) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, measureReal_def] using hr

end Balanced.PatternModel

end OAI
