import Mathlib.Topology.MetricSpace.HausdorffDimension

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Metric
open scoped ENNReal NNReal

noncomputable def hausdorffContent {X : Type*} [EMetricSpace X] (s : ℝ) (E : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : E ⊆ ⋃ n, U n), ∑' n, (Metric.ediam (U n))^s

theorem content_le_cover {X : Type*} [EMetricSpace X] (s : ℝ) (E : Set X)
    (U : ℕ → Set X) (hU : E ⊆ ⋃ n, U n) :
    hausdorffContent s E ≤ ∑' n, (Metric.ediam (U n))^s :=
  iInf_le_of_le U (iInf_le _ hU)

theorem cover_diameter_bound {X : Type*} [EMetricSpace X] {s : ℝ} (hs : 0 < s)
    (U : ℕ → Set X) {r : ℝ≥0∞}
    (hcost : (∑' n, (Metric.ediam (U n))^s) ≤ r^s) (n : ℕ) :
    Metric.ediam (U n) ≤ r := by
  apply (ENNReal.rpow_le_rpow_iff hs).mp
  exact (ENNReal.le_tsum n).trans hcost

theorem hausdorffMeasure_zero_of_content_zero {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {s : ℝ} (hs : 0 < s) (E : Set X) (hzero : hausdorffContent s E = 0) :
    Measure.hausdorffMeasure s E = 0 := by
  rw [Measure.hausdorffMeasure_apply]
  apply le_antisymm _ bot_le
  refine iSup_le fun r => iSup_le fun hr => ?_
  apply le_of_forall_gt
  intro ε hε
  have hrpow : 0 < r^s := by positivity
  have hc : hausdorffContent s E < min ε (r^s) := by
    rw [hzero]
    exact lt_min hε hrpow
  obtain ⟨U,hU⟩ := iInf_lt_iff.mp hc
  obtain ⟨hcover,hcost⟩ := iInf_lt_iff.mp hU
  have hdiam : ∀ n, Metric.ediam (U n) ≤ r :=
    cover_diameter_bound hs U (hcost.le.trans (min_le_right _ _))
  calc
    _ ≤ ∑' n, ⨆ _ : (U n).Nonempty, (Metric.ediam (U n))^s :=
      iInf_le_of_le U (iInf_le_of_le hcover (iInf_le _ hdiam))
    _ ≤ ∑' n, (Metric.ediam (U n))^s :=
      ENNReal.tsum_le_tsum (fun _ => iSup_le fun _ => le_rfl)
    _ < ε := hcost.trans_le (min_le_left _ _)

theorem content_positive_of_lt_dimH {X : Type*} [EMetricSpace X]
    (E : Set X) {s : ℝ≥0} (hs : 0 < s) (hd : (s : ℝ≥0∞) < dimH E) :
    0 < hausdorffContent (s : ℝ) E := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  by_contra h
  have hc : hausdorffContent (s : ℝ) E = 0 := le_antisymm (not_lt.mp h) bot_le
  have hz := hausdorffMeasure_zero_of_content_zero (by exact_mod_cast hs) E hc
  have ht := hausdorffMeasure_of_lt_dimH hd
  rw [hz] at ht
  exact ENNReal.zero_ne_top ht

end PlanarFalconer

end OAI
