import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

/-! # Counting heavy members of a finite family with bounded overlap -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {X ι : Type*} [MeasurableSpace X]
attribute [local instance] Classical.propDecidable

theorem finite_measure_sum_le_overlap (μ : Measure X) (I : Finset ι) (U : ι → Set X)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (L : ℕ)
    (hoverlap : ∀ x, (I.filter (fun i => x ∈ U i)).card ≤ L) :
    ∑ i ∈ I, μ (U i) ≤ (L:ℝ≥0∞)*μ univ := by
  classical
  have hp (x : X) : (∑ i ∈ I, (U i).indicator (fun _ => (1:ℝ≥0∞)) x) =
      ((I.filter (fun i => x ∈ U i)).card:ℝ≥0∞) := by
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter]
    simp
  calc
    _ = ∑ i ∈ I, ∫⁻ x, (U i).indicator (fun _ => (1:ℝ≥0∞)) x ∂μ :=
      Finset.sum_congr rfl (fun i hi => (lintegral_indicator_one (hU i hi)).symm)
    _ = ∫⁻ x, ∑ i ∈ I, (U i).indicator (fun _ => (1:ℝ≥0∞)) x ∂μ := by
      rw [lintegral_finsetSum' I (fun i hi => (measurable_const.indicator (hU i hi)).aemeasurable)]
    _ ≤ ∫⁻ _x, (L:ℝ≥0∞) ∂μ := lintegral_mono (fun x => by
      rw [hp]
      exact Nat.cast_le.mpr (hoverlap x))
    _ = _ := lintegral_const _

theorem heavy_family_card_bound (μ : Measure X) (I : Finset ι) (U : ι → Set X)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (L : ℕ)
    (hoverlap : ∀ x, (I.filter (fun i => x ∈ U i)).card ≤ L)
    (F : ℝ≥0∞) (hheavy : ∀ i ∈ I, F ≤ μ (U i)) :
    (I.card:ℝ≥0∞)*F ≤ (L:ℝ≥0∞)*μ univ := by
  calc
    _ = ∑ _i ∈ I, F := by simp
    _ ≤ ∑ i ∈ I, μ (U i) := Finset.sum_le_sum hheavy
    _ ≤ _ := finite_measure_sum_le_overlap μ I U hU L hoverlap

end Falconer

end OAI
