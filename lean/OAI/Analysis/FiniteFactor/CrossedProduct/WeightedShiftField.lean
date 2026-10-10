import OAI.Analysis.FiniteFactor.CrossedProduct.FieldAlgebra
import OAI.Analysis.FiniteFactor.Matrix.Covariance

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceMatrixEntry_sourceOperator_pow (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (q : ℕ) (m : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      sourceMatrixEntry (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ^ q) k m x =
        if k = m + (q : ℤ) then
          (sourceCocycle θ sourceLogWeight q (coordinateRotate θ m x) : ℂ) else 0 := by
  have hb := (sourceShiftNIndex_preserving SourceCoordinate q).quasiMeasurePreserving.ae
    (sourceBasis_coe m)
  filter_upwards [source_ae_all_fibers (sourceOperator_pow_apply_ae θ sourceLogWeight hθ.nonneg
    sourceLogWeight_nonneg hθ.summable q (sourceBasis m)), source_ae_all_fibers hb] with x hp hb k
  unfold sourceMatrixEntry
  rw [hp, hb]
  simp only [sourceShiftNIndex]
  by_cases hk : k = m + (q : ℤ)
  · simp [hk]
  · have he : k - (q : ℤ) ≠ m := by omega
    simp [he, hk]

/-- The field of each power of the original quasinilpotent operator acts by
its verified source cocycle, simultaneously on every l2 vector. -/
theorem sourceOperatorField_sourceOperator_pow (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (q : ℕ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ (v : SourceFiberHilbert) (k : ℤ),
      (sourceOperatorField
        (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ^ q) x v) k =
        (sourceCocycle θ sourceLogWeight q (coordinateRotate θ (k - (q : ℤ)) x) : ℂ) *
          v (k - (q : ℤ)) := by
  have hm := ae_all_iff.mpr (sourceMatrixEntry_sourceOperator_pow θ hθ q)
  filter_upwards [sourceOperatorField_entries_ae θ (pow_mem (staged_sourceOperator_mem θ hθ) q),
    hm] with x he hm v k
  rw [fiberOperator_action]
  simp_rw [he, hm]
  have ht (n : ℤ) :
      (if k = n + (q : ℤ) then
        (sourceCocycle θ sourceLogWeight q (coordinateRotate θ n x) : ℂ) else 0) * v n =
      if n = k - (q : ℤ) then
        (sourceCocycle θ sourceLogWeight q (coordinateRotate θ (k - (q : ℤ)) x) : ℂ) *
          v (k - (q : ℤ)) else 0 := by
    by_cases hn : n = k - (q : ℤ)
    · have hk : k = n + (q : ℤ) := by omega
      rw [ite_eq_left hk, ite_eq_left hn, hn]
    · have hk : k ≠ n + (q : ℤ) := by omega
      rw [ite_eq_right hk, ite_eq_right hn, zero_mul]
  simp_rw [ht]
  simp

/-- Covariance for the actual field's matrix, with all integer indices on one
conull set. This is the coordinate form of conjugation by the fiber shift. -/
theorem sourceOperatorField_covariance (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ r n k : ℤ,
      (sourceOperatorField H (coordinateRotate θ r x) (lp.single 2 n (1 : ℂ))) k =
        (sourceOperatorField H x (lp.single 2 (n+r) (1 : ℂ))) (k+r) := by
  have he : ∀ᵐ x ∂sourceBaseMeasure, ∀ r : ℤ, ∀ k n : ℤ,
      (sourceOperatorField H (coordinateRotate θ r x) (lp.single 2 n (1 : ℂ))) k =
        sourceMatrixEntry H k n (coordinateRotate θ r x) := by
    rw [ae_all_iff]
    intro r
    exact (coordinateRotate_preserving θ r).quasiMeasurePreserving.ae
      (sourceOperatorField_entries_ae θ hH)
  filter_upwards [he, sourceOperatorField_entries_ae θ hH,
    sourceMatrixEntry_covariance_all θ hH] with x he hx hc r n k
  rw [he, hx, hc]

end
end FiniteFactor

end OAI
