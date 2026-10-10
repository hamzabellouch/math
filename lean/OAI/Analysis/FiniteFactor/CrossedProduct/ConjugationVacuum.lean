import OAI.Analysis.FiniteFactor.CrossedProduct.Reflection
import OAI.Analysis.FiniteFactor.CrossedProduct.VacuumSeparating

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Reflection of each total vacuum test equals its commutant adjoint on the vacuum. -/
theorem sourceConjugation_fiberIndicator (θ : SourceCoordinate → ℝ)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ) :
    sourceConjugation θ (sourceFiberIndicator A hA n) =
      star (sourceScalar (sourceBaseIndicator A hA) * sourceCommutantRotation θ n) sourceVacuum := by
  rw [star_mul, sourceScalar_star, sourceCommutantRotation_star]
  apply Lp.ext
  have hf := (sourceReflectionIndex_preserving θ).quasiMeasurePreserving.ae
    (sourceFiberIndicator_coe A hA n)
  have hs := (sourceTransportIndex_preserving θ (-n) (-n)).quasiMeasurePreserving.ae
    (sourcePi_apply_ae (fun _ => 0) (sourceBaseStar (sourceBaseIndicator A hA)) sourceVacuum)
  have hv := (sourceTransportIndex_preserving θ (-n) (-n)).quasiMeasurePreserving.ae sourceVacuum_coe
  filter_upwards [sourceConjugation_apply_ae θ (sourceFiberIndicator A hA n), hf,
    sourceTransport_apply_ae θ (-n) (-n)
      (sourcePi (fun _ => 0) (sourceBaseStar (sourceBaseIndicator A hA)) sourceVacuum), hs, hv]
      with z h1 h2 h3 h4 h5
  change (sourceConjugation θ (sourceFiberIndicator A hA n)) z =
    (sourceTransport θ (-n) (-n) (sourcePi (fun _ => 0) (sourceBaseStar (sourceBaseIndicator A hA)) sourceVacuum)) z
  rw [h1,h2,h3,h4,h5]
  have he : coordinateRotate (fun _ : SourceCoordinate => 0) (z.2 - -n)
      (coordinateRotate θ (-n) z.1) = coordinateRotate θ (-n) z.1 := by
    funext i
    simp [coordinateRotate, Int.fract_fract]
  unfold sourcePiSymbol sourceTransportIndex
  dsimp only
  rw [he]
  by_cases hn : z.2 = -n
  · by_cases ha : coordinateRotate θ (-n) z.1 ∈ A <;>
      simp [sourceReflectionIndex, sourceBaseStar, sourceBaseIndicator, hn, ha]
  · have hn' : -z.2 ≠ n := by omega
    have hn'' : z.2 + n ≠ 0 := by omega
    simp [sourceReflectionIndex, sourceBaseStar, sourceBaseIndicator, hn', hn'']

/-- The actual reflection sends H e_0 to H* e_0 for every source-algebra element. -/
theorem sourceConjugation_algebra_vacuum (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    sourceConjugation θ (H sourceVacuum) = star H sourceVacuum := by
  apply sub_eq_zero.mp
  apply sourceFiberIndicators_total
  intro A hA n
  rw [inner_sub_right]
  apply sub_eq_zero.mpr
  rw [sourceConjugation_inner_symm, sourceConjugation_fiberIndicator,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hr := congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
    T sourceVacuum) (sourceAlgebra_commutes_rotation θ hH n)
  rw [sourceFiberIndicator_eq_orbit θ A hA n]
  congr 1
  change sourceScalar (sourceBaseIndicator A hA) (sourceCommutantRotation θ n (H sourceVacuum)) =
    H (sourceScalar (sourceBaseIndicator A hA) (sourceCommutantRotation θ n sourceVacuum))
  have hs' := congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
    T (sourceCommutantRotation θ n sourceVacuum))
    (sourceAlgebra_commutes_scalar θ hH (sourceBaseIndicator A hA))
  change sourceCommutantRotation θ n (H sourceVacuum) = H (sourceCommutantRotation θ n sourceVacuum) at hr
  change sourceScalar (sourceBaseIndicator A hA) (H (sourceCommutantRotation θ n sourceVacuum)) = _ at hs'
  rw [hr]
  exact hs'

end
end FiniteFactor

end OAI
