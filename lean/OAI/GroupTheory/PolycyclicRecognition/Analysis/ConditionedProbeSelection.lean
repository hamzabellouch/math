import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Regular

namespace OAI

/-! # Keeping positive probe mass after conditioning the starting sample -/

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal

/-- If joint failures occupy less than half the mass of the starting
profile event, some starting sample in that event retains at least half
of the independent probes. No conditioning on a singleton is used. -/
theorem exists_start_with_half_good_probes
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set X) (bad : Set (X × Y)) (hE : MeasurableSet E) (hbad : MeasurableSet bad)
    (hsmall : (μ.prod ν) bad < (1 / 2 : ℝ≥0∞) * μ E) :
    ∃ x ∈ E, (1 / 2 : ℝ≥0∞) ≤ ν {y | (x, y) ∉ bad} := by
  by_contra hnone
  push Not at hnone
  have hfiber (x : X) (hx : x ∈ E) :
      (1 / 2 : ℝ≥0∞) ≤ ν {y | (x, y) ∈ bad} := by
    by_contra hlt
    have hb : ν {y | (x, y) ∈ bad} < (1 / 2 : ℝ≥0∞) := lt_of_not_ge hlt
    have hs : MeasurableSet {y | (x, y) ∈ bad} :=
      (measurable_const.prodMk measurable_id) hbad
    have hh := ENNReal.add_lt_add hb (hnone x hx)
    change ν {y | (x, y) ∈ bad} + ν ({y | (x, y) ∈ bad}ᶜ) <
      (1 / 2 : ℝ≥0∞) + 1 / 2 at hh
    rw [prob_add_prob_compl hs] at hh
    rw [ENNReal.add_halves] at hh
    exact (lt_irrefl (1 : ℝ≥0∞)) hh
  have hbound : (1 / 2 : ℝ≥0∞) * μ E ≤ (μ.prod ν) bad := by
    rw [Measure.prod_apply hbad]
    calc
      _ = ∫⁻ x, E.indicator (fun _ => (1 / 2 : ℝ≥0∞)) x ∂μ := by
        rw [lintegral_indicator hE]
        simp
      _ ≤ _ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ E
        · rw [indicator_of_mem hx]
          exact hfiber x hx
        · rw [indicator_of_notMem hx]
          exact zero_le
  exact (not_lt_of_ge hbound) hsmall

/-- Inner regularity retains a compact positive-volume probe set at that
same starting sample; the original starting-event probability is not lost. -/
theorem exists_start_with_compact_good_probes
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [TopologicalSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [ν.InnerRegular]
    (E : Set X) (bad : Set (X × Y)) (hE : MeasurableSet E) (hbad : MeasurableSet bad)
    (hsmall : (μ.prod ν) bad < (1 / 2 : ℝ≥0∞) * μ E) :
    ∃ x ∈ E, ∃ K : Set Y, IsCompact K ∧ K ⊆ {y | (x, y) ∉ bad} ∧
      (1 / 4 : ℝ≥0∞) < ν K := by
  obtain ⟨x, hx, hm⟩ := exists_start_with_half_good_probes μ ν E bad hE hbad hsmall
  have hgood : MeasurableSet {y | (x, y) ∉ bad} :=
    ((measurable_const.prodMk measurable_id) hbad).compl
  have hquarter : (1 / 4 : ℝ≥0∞) < 1 / 2 := by
    exact (ENNReal.div_lt_div_iff_right (by norm_num) (by simp)).mpr (by norm_num)
  obtain ⟨K, hK, hc, hmass⟩ := hgood.exists_lt_isCompact (hquarter.trans_le hm)
  exact ⟨x, hx, K, hc, hK, hmass⟩

end PolycyclicRecognition

end OAI
