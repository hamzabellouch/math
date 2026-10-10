import OAI.Analysis.FiniteFactor.CrossedProduct.FiberTotal

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

/-- The actual constant e_0 vector separates the source double commutant. -/
theorem sourceVacuum_separating (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (hv : H sourceVacuum = 0) : H = 0 := by
  have hkill (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ) :
      H (sourceFiberIndicator A hA n) = 0 := by
    rw [sourceFiberIndicator_eq_orbit θ A hA n]
    have hs := congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      T (sourceCommutantRotation θ n sourceVacuum))
      (sourceAlgebra_commutes_scalar θ hH (sourceBaseIndicator A hA))
    have hr := congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      T sourceVacuum) (sourceAlgebra_commutes_rotation θ hH n)
    change sourceScalar (sourceBaseIndicator A hA) (H (sourceCommutantRotation θ n sourceVacuum)) =
      H (sourceScalar (sourceBaseIndicator A hA) (sourceCommutantRotation θ n sourceVacuum)) at hs
    change sourceCommutantRotation θ n (H sourceVacuum) = H (sourceCommutantRotation θ n sourceVacuum) at hr
    rw [← hs, ← hr, hv]
    simp
  have hstar : star H = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    change star H f = 0
    apply sourceFiberIndicators_total
    intro A hA n
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, hkill]
    simp
  exact star_eq_zero.mp hstar

/-- Faithfulness on squares of the actual normal vacuum functional. -/
theorem sourceVacuumFunctional_square_eq_zero_iff (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    sourceVacuumFunctional (star H * H) = 0 ↔ H = 0 := by
  constructor
  · intro hz
    rw [sourceVacuumFunctional_square] at hz
    exact sourceVacuum_separating θ hH (inner_self_eq_zero.mp hz)
  · rintro rfl
    simp [sourceVacuumFunctional]

end
end FiniteFactor

end OAI
