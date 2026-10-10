import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

namespace OAI

/-! Subtraction for locally finite canonical mass. Cancellation is checked
on finite restrictions, so no finite total-mass assumption is needed. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace SLEExactGauge

theorem sigmaFinite_sub_add_cancel_of_le
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [SigmaFinite ν]
    (hle : ν ≤ μ) : μ - ν + ν = μ := by
  apply Measure.ext_of_iUnion_eq_univ (iUnion_spanningSets ν)
  intro n
  rw [Measure.restrict_add,Measure.restrict_sub_eq_restrict_sub_restrict
    (measurableSet_spanningSets ν n)]
  have : Fact (ν (spanningSets ν n) < ⊤) := ⟨measure_spanningSets_lt_top ν n⟩
  exact Measure.sub_add_cancel_of_le (Measure.restrict_mono le_rfl hle)

theorem sub_apply_of_finite_restriction
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} (hle : ν ≤ μ)
    {A : Set X} (hA : MeasurableSet A) (hνA : ν A ≠ ⊤) :
    (μ - ν) A = μ A - ν A := by
  have : Fact (ν A < ⊤) := ⟨hνA.lt_top⟩
  calc
    (μ - ν) A = ((μ - ν).restrict A) univ := by simp
    _ = (μ.restrict A - ν.restrict A) univ := by
      rw [Measure.restrict_sub_eq_restrict_sub_restrict hA]
    _ = μ.restrict A univ - ν.restrict A univ :=
      Measure.sub_apply MeasurableSet.univ (Measure.restrict_mono le_rfl hle)
    _ = μ A - ν A := by simp

theorem sub_le_sub_right_of_le
    {X : Type*} [MeasurableSpace X] {μ ν ξ : Measure X} [SigmaFinite ξ]
    (hξ : ξ ≤ ν) (hμν : μ ≤ ν) : μ - ξ ≤ ν - ξ := by
  apply Measure.sub_le_of_le_add
  rw [sigmaFinite_sub_add_cancel_of_le hξ]
  exact hμν

end SLEExactGauge

end

end OAI
