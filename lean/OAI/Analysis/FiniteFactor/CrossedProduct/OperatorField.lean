import OAI.Analysis.FiniteFactor.Matrix.Bounds
import OAI.Analysis.FiniteFactor.Matrix.Integrals
import OAI.Analysis.FiniteFactor.BoundedMatrixOperator

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceMatrixGood (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (x : SourceCoordinate → ℝ) : Prop :=
  ∀ (s t : Finset ℤ) (a : ℤ → ℂ),
    (∑ k ∈ t, ‖∑ n ∈ s, a n * sourceMatrixEntry H k n x‖ ^ 2) ≤
      ‖H‖ ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2

/-- A Borel good set, removing just one null set for algebra elements. -/
def sourceFieldGoodSet
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    Set (SourceCoordinate → ℝ) :=
  (toMeasurable sourceBaseMeasure {x | ¬ sourceMatrixGood H x})ᶜ

theorem sourceFieldGoodSet_measurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    MeasurableSet (sourceFieldGoodSet H) := (measurableSet_toMeasurable _ _).compl

theorem sourceFieldGoodSet_good
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    {x : SourceCoordinate → ℝ} (hx : x ∈ sourceFieldGoodSet H) : sourceMatrixGood H x := by
  by_contra hn
  exact hx (subset_toMeasurable sourceBaseMeasure _ hn)

theorem sourceFieldGoodSet_ae (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) : ∀ᵐ x ∂sourceBaseMeasure, x ∈ sourceFieldGoodSet H := by
  have hb : ∀ᵐ x ∂sourceBaseMeasure, sourceMatrixGood H x := sourceMatrix_finite_bound_all θ hH
  rw [ae_iff] at hb ⊢
  simpa [sourceFieldGoodSet, measure_toMeasurable] using hb

/-- The actual bounded operator field, extended by zero on a Borel null set. -/
def sourceOperatorField
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (x : SourceCoordinate → ℝ) : SourceFiberHilbert →L[ℂ] SourceFiberHilbert := by
  classical
  exact if hx : x ∈ sourceFieldGoodSet H then
    boundedMatrixOperator (fun k n => sourceMatrixEntry H k n x) ‖H‖
      (sourceFieldGoodSet_good H hx)
  else 0

theorem sourceOperatorField_norm
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (x) :
    ‖sourceOperatorField H x‖ ≤ ‖H‖ := by
  classical
  unfold sourceOperatorField
  split_ifs
  · exact boundedMatrixOperator_norm _ _ _ (norm_nonneg H)
  · simp

theorem sourceOperatorField_entry
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) (x) :
    (sourceOperatorField H x (lp.single 2 n (1 : ℂ))) k =
      (sourceFieldGoodSet H).indicator (sourceMatrixEntry H k n) x := by
  classical
  unfold sourceOperatorField
  split_ifs with hx
  · rw [Set.indicator_of_mem hx]
    exact boundedMatrixOperator_entry _ _ _ (norm_nonneg H) k n
  · simp [hx]

theorem sourceOperatorField_entry_measurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) :
    Measurable (fun x => (sourceOperatorField H x (lp.single 2 n (1 : ℂ))) k) := by
  simp_rw [sourceOperatorField_entry]
  exact (sourceMatrixEntry_measurable H k n).indicator (sourceFieldGoodSet_measurable H)

/-- Field entries recover the original coefficients on one conull set. -/
theorem sourceOperatorField_entries_ae (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k n : ℤ,
      (sourceOperatorField H x (lp.single 2 n (1 : ℂ))) k = sourceMatrixEntry H k n x := by
  filter_upwards [sourceFieldGoodSet_ae θ hH] with x hx k n
  rw [sourceOperatorField_entry, Set.indicator_of_mem hx]

end
end FiniteFactor

end OAI
