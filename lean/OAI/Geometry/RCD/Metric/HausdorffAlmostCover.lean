import OAI.Geometry.RCD.Transport.PointedMidpointSets
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

/-! # Hausdorff bounds from arbitrarily fine covers outside a Hausdorff-null set -/

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem hausdorff_le_of_ae_small_covers {n : ℕ} (d : ℝ)
    (s : Set (Euclidean n)) (C : ℝ≥0∞)
    (hcover : ∀ δ : ℝ≥0∞, 0 < δ → ∃ (ι : Type) (_ : Countable ι)
      (t : ι → Set (Euclidean n)),
      (∀ i, ediam (t i) ≤ δ) ∧
      Measure.hausdorffMeasure d (s \ ⋃ i, t i)=0 ∧
      (∑' i, ediam (t i)^d) ≤ C) :
    Measure.hausdorffMeasure d s ≤ C := by
  change (Measure.mkMetric (fun r => r^d)).toOuterMeasure s ≤ C
  rw [Measure.mkMetric_toOuterMeasure]
  simp only [OuterMeasure.mkMetric,OuterMeasure.mkMetric',OuterMeasure.iSup_apply,iSup_le_iff]
  intro δ hδ
  obtain ⟨ι,hι,t,ht,hnull,hsum⟩ := hcover δ hδ
  let : Countable ι := hι
  let ν := OuterMeasure.mkMetric'.pre (fun A : Set (Euclidean n) => ediam A^d) δ
  have hν : ν ≤ OuterMeasure.mkMetric (fun r => r^d) :=
    le_iSup₂_of_le δ hδ le_rfl
  have hz : ν (s \ ⋃ i, t i) = 0 := by
    apply le_antisymm _ bot_le
    calc
      ν (s \ ⋃ i, t i) ≤ OuterMeasure.mkMetric (fun r => r^d) (s \ ⋃ i, t i) := hν _
      _ = 0 := by
        rwa [← Measure.mkMetric_toOuterMeasure]
  change ν s ≤ C
  calc
    ν s ≤ ν ((⋃ i, t i) ∪ (s \ ⋃ i, t i)) := measure_mono (by tauto_set)
    _ ≤ ν (⋃ i, t i)+ν (s \ ⋃ i, t i) := measure_union_le _ _
    _ ≤ (∑' i, ν (t i))+0 := add_le_add (measure_iUnion_le _) hz.le
    _ = ∑' i, ν (t i) := add_zero _
    _ ≤ ∑' i, ediam (t i)^d := ENNReal.tsum_le_tsum fun i => OuterMeasure.mkMetric'.pre_le (ht i)
    _ ≤ C := hsum

end RegularPointCoordinates

end

end OAI
