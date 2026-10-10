import OAI.Analysis.FiniteFactor.Sampling.IntervalError
import OAI.Analysis.FiniteFactor.CrossedProduct.PhaseMarginal

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

def samplingBoundary (a b δ : ℝ) : Set ℝ :=
  (Set.Icc δ (1-δ))ᶜ ∪ Set.Icc (a-δ) (a+δ) ∪ Set.Icc (b-δ) (b+δ)

theorem samplingBoundary_measurable (a b δ : ℝ) : MeasurableSet (samplingBoundary a b δ) :=
  (measurableSet_Icc.compl.union measurableSet_Icc).union measurableSet_Icc

theorem samplingBoundary_measure (a b δ : ℝ) (hδ : 0 ≤ δ) :
    unitIntervalMeasure (samplingBoundary a b δ) ≤ ENNReal.ofReal (6*δ) := by
  have hband (a : ℝ) : unitIntervalMeasure (Set.Icc (a-δ) (a+δ)) ≤ ENNReal.ofReal (2*δ) := by
    calc
      _ ≤ volume (Set.Icc (a-δ) (a+δ)) := Measure.restrict_le_self _
      _ = _ := by rw [Real.volume_Icc]; congr 1; ring
  calc
    _ ≤ unitIntervalMeasure ((Set.Icc δ (1-δ))ᶜ ∪ Set.Icc (a-δ) (a+δ)) +
        unitIntervalMeasure (Set.Icc (b-δ) (b+δ)) := measure_union_le _ _
    _ ≤ unitIntervalMeasure (Set.Icc δ (1-δ))ᶜ +
        unitIntervalMeasure (Set.Icc (a-δ) (a+δ)) +
        unitIntervalMeasure (Set.Icc (b-δ) (b+δ)) := by gcongr; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (2*δ) + ENNReal.ofReal (2*δ) + ENNReal.ofReal (2*δ) := by
      gcongr
      · exact unitInterval_middle_compl δ hδ
      · exact hband a
      · exact hband b
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

theorem samplingSmooth_indicator_error_le_one (H : ℕ) (hH : 0 < H) (E : Set ℝ) (t : ℝ) :
    |samplingSmooth H E t - E.indicator (fun _ => (1 : ℝ)) t| ≤ 1 := by
  have h := samplingSmooth_bounds H hH E t
  by_cases ht : t ∈ E
  · rw [Set.indicator_of_mem ht]
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  · rw [Set.indicator_of_notMem ht, sub_zero, abs_of_nonneg h.1]
    exact h.2

/-- The interval smoothing error integrated under any actual phase law with
density bounded by two. Only one-dimensional domination is used. -/
theorem samplingSmooth_expected_error (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν ≤ (2 : ℝ≥0∞) • unitIntervalMeasure) (H : ℕ) (hH : 0 < H)
    (a b δ : ℝ) (hδ : 0 < δ) :
    (∫ t, |samplingSmooth H (Set.Icc a b) t -
      (Set.Icc a b).indicator (fun _ => (1 : ℝ)) t| ∂ν) ≤
      12*δ + 1/(4*(H : ℝ)*δ^2) := by
  let E := Set.Icc a b
  let B := samplingBoundary a b δ
  let C := 1/(4*(H : ℝ)*δ^2)
  let f := fun t => |samplingSmooth H E t - E.indicator (fun _ => (1 : ℝ)) t|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBm : MeasurableSet B := samplingBoundary_measurable a b δ
  have hfm : Measurable f := by
    have hi : Measurable (E.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator measurableSet_Icc
    simpa only [Real.norm_eq_abs, Pi.sub_apply, f] using ((samplingSmooth_continuous H E).measurable.sub hi).norm
  have hfi : Integrable f ν := (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
      exact samplingSmooth_indicator_error_le_one H hH E t))
  have hle (t : ℝ) : f t ≤ B.indicator (fun _ => (1 : ℝ)) t + C := by
    by_cases ht : t ∈ B
    · rw [Set.indicator_of_mem ht]
      exact (samplingSmooth_indicator_error_le_one H hH E t).trans (by linarith)
    · rw [Set.indicator_of_notMem ht, zero_add]
      have hn := not_or.mp ht
      have hn' := not_or.mp hn.1
      have hmid : t ∈ Set.Icc δ (1-δ) := by simpa only [Set.mem_compl_iff, not_not] using hn'.1
      have ha : δ < |t-a| := by
        by_contra hh
        have hab := abs_le.mp (le_of_not_gt hh)
        exact hn'.2 ⟨by linarith [hab.1], by linarith [hab.2]⟩
      have hb : δ < |t-b| := by
        by_contra hh
        have hab := abs_le.mp (le_of_not_gt hh)
        exact hn.2 ⟨by linarith [hab.1], by linarith [hab.2]⟩
      exact samplingSmooth_interval_error H hH a b δ t hδ hmid.1 hmid.2 ha hb
  have hBμ : ν B ≤ ENNReal.ofReal (12*δ) := by
    calc
      _ ≤ ((2 : ℝ≥0∞) • unitIntervalMeasure) B := hν B
      _ = 2 * unitIntervalMeasure B := rfl
      _ ≤ 2 * ENNReal.ofReal (6*δ) := by gcongr; exact samplingBoundary_measure a b δ hδ.le
      _ = _ := by rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; congr 1; ring
  have hBreal : (ν B).toReal ≤ 12*δ := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBμ
    rwa [ENNReal.toReal_ofReal (by positivity)] at hh
  have hh := integral_mono_ae hfi (((integrable_const (1 : ℝ)).indicator hBm).add (integrable_const C))
    (Filter.Eventually.of_forall hle)
  simp only [Pi.add_apply] at hh
  rw [integral_add ((integrable_const (1 : ℝ)).indicator hBm) (integrable_const C), integral_indicator hBm] at hh
  simp [measureReal_def] at hh
  change (∫ t, f t ∂ν) ≤ 12*δ+C
  linarith

end
end FiniteFactor

end OAI
