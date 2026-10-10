import OAI.Analysis.FiniteFactor.CrossedProduct.CentralDiagonal
import OAI.Analysis.FiniteFactor.Fiber.Shift
import Mathlib.Algebra.Ring.Periodic

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceOperatorField_shift (θ : SourceCoordinate → ℝ) :
    ∀ᵐ x ∂sourceBaseMeasure, sourceOperatorField (sourceShift SourceCoordinate) x = fiberShift 1 := by
  classical
  have hm := ae_all_iff.mpr sourceMatrixEntry_shift
  filter_upwards [hm,sourceOperatorField_entries_ae θ (sourceShift_mem θ)] with x hm he
  apply fiberOperator_ext
  intro k n
  rw [he,hm]
  rw [fiberShift_single]
  by_cases hk : k = n+1
  · subst k; simp [lp.single_apply]
  · simp [lp.single_apply,hk]

/-- Commutation with the bilateral shift makes all diagonal coefficients equal. -/
theorem fiber_commuting_shift_diagonal (A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hc : A*fiberShift 1 = fiberShift 1*A) (n : ℤ) :
    A (lp.single 2 n (1 : ℂ)) n = A (lp.single 2 0 (1 : ℂ)) 0 := by
  have hperiod : Function.Periodic
      (fun k : ℤ => A (lp.single 2 k (1 : ℂ)) k) 1 := by
    intro k
    have he := congrArg (fun T : SourceFiberHilbert →L[ℂ] SourceFiberHilbert =>
      T (lp.single 2 k (1 : ℂ)) (k+1)) hc
    change A (fiberShift 1 (lp.single 2 k (1 : ℂ))) (k+1) =
      (fiberShift 1 (A (lp.single 2 k (1 : ℂ)))) (k+1) at he
    simpa only [fiberShift_single,fiberShift_apply,add_sub_cancel_right] using he
  simpa using hperiod.int_mul_eq n

/-- The scalar coefficient is the actual field's 00 entry. -/
def sourceCentralCoefficient
    (A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (x : SourceCoordinate → ℝ) : ℂ := sourceOperatorField A x (lp.single 2 0 (1 : ℂ)) 0

theorem sourceCentralCoefficient_measurable
    (A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    Measurable (sourceCentralCoefficient A) := sourceOperatorField_entry_measurable A 0 0

/-- Every central element of the original algebra is a scalar field. The
scalar may still depend on x; ergodicity is needed to make it constant. -/
theorem sourceCentral_scalar_field (θ : SourceCoordinate → ℝ) (hr : SourceRationalIndependent θ)
    {A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ)
    (hcentral : ∀ B ∈ sourceAlgebra θ, A*B = B*A) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField A x = sourceCentralCoefficient A x • (1 : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) := by
  filter_upwards [sourceCentral_offDiagonal_zero θ hr hA hcentral,sourceOperatorField_shift θ,
    sourceOperatorField_commute θ hA (sourceShift_mem θ) (hcentral _ (sourceShift_mem θ))]
    with x hd hs hc
  rw [hs] at hc
  apply fiberOperator_ext
  intro k n
  change sourceOperatorField A x (lp.single 2 n (1 : ℂ)) k =
    sourceCentralCoefficient A x * (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) k
  by_cases hnk : n = k
  · subst k
    simpa [lp.single_apply,sourceCentralCoefficient] using fiber_commuting_shift_diagonal _ hc n
  · rw [hd n k hnk]
    simp [lp.single_apply,hnk]

/-- Covariance makes the actual scalar field invariant under every integer
rotation. No ergodicity hypothesis or constant-value conclusion is inserted. -/
theorem sourceCentralCoefficient_rotation_invariant
    (θ : SourceCoordinate → ℝ) (hr : SourceRationalIndependent θ)
    {A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ)
    (hcentral : ∀ B ∈ sourceAlgebra θ, A*B = B*A) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ,
      sourceCentralCoefficient A (coordinateRotate θ n x) = sourceCentralCoefficient A x := by
  filter_upwards [sourceOperatorField_covariance θ hA,sourceCentral_scalar_field θ hr hA hcentral]
    with x hc hs n
  change sourceOperatorField A (coordinateRotate θ n x) (lp.single 2 0 (1 : ℂ)) 0 = _
  rw [hc,zero_add,hs]
  change sourceCentralCoefficient A x * (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) n = _
  simp [lp.single_apply]

end
end FiniteFactor

end OAI
