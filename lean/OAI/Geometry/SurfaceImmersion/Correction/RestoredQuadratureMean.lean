import OAI.Geometry.SurfaceImmersion.Geometry.RealRestoredMetric
import OAI.Geometry.SurfaceImmersion.Correction.GlobalQuadraticModes

namespace OAI

/-! Transport the actual zero Fourier coefficient through supported atlas restoration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

local instance restoredMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance restoredMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance restoredMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance restoredMeanSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredMeanSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem restored_zeroPhase (i : A.centers) (τ : ℝ)
    (φ : SmallModes.Base → ℝ) (Z : SmallModes.Base → Fin 4 → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z)
    (hs : tsupport Z ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    let Φ := restore (i : M) (A.outer i) (φ ∘ planeCoordinateIsometry)
    let W := restore (i : M) (A.outer i) (Z ∘ planeCoordinateIsometry)
    A.tensorPlaneRestore (fun j x => (A.planeWeight j x)^2 •
      RealModes.phaseZeroTensor τ (A.vectorPlaneRead j Φ) (A.vectorPlaneRead j W) x) =
    A.bundleRestore A.tensorTriv i (fun y =>
      fiberFromThree (RealModes.phaseZeroTensor τ φ Z (planeCoordinateIsometry y))) := by
  dsimp only
  let Φ := restore (i : M) (A.outer i) (φ ∘ planeCoordinateIsometry)
  let W := restore (i : M) (A.outer i) (Z ∘ planeCoordinateIsometry)
  let ZI := fun x => Complex.I • Z x
  have hΦ : ContMDiff planeModel 𝓘(ℝ) ∞ Φ := restore_smooth (i : M)
    (A.outer_smooth i) (A.outer_support i) (hφ.comp planeCoordinateIsometry.contDiff)
  have hW : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ W := restore_smooth (i : M)
    (A.outer_smooth i) (A.outer_support i) (hZ.comp planeCoordinateIsometry.contDiff)
  have hZI : ContDiff ℝ ∞ ZI := (contDiff_const (c := Complex.I)).smul hZ
  have hsI : tsupport ZI ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    (tsupport_smul_subset_right (fun _ => Complex.I) Z).trans hs
  have hWI : (fun p => Complex.I • W p) =
      restore (i : M) (A.outer i) (ZI ∘ planeCoordinateIsometry) := by
    funext p
    by_cases hp : p ∈ (chart (i : M)).source
    · simp only [W,ZI,restore,indicator_of_mem hp,Function.comp_apply]
      exact smul_comm _ _ _
    · simp only [W,restore,indicator_of_notMem hp,smul_zero]
  have hdisp := contDiffOn_univ.mp (RealModes.contDiffOn_displacement hφ.contDiffOn hZ.contDiffOn τ)
  have hdispI := contDiffOn_univ.mp (RealModes.contDiffOn_displacement hφ.contDiffOn hZI.contDiffOn τ)
  have hsdisp : tsupport (QuadraticMean.displacement τ φ Z) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    (surfaceMode_tsupport τ φ Z).trans hs
  have hsdispI : tsupport (QuadraticMean.displacement τ φ ZI) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    (surfaceMode_tsupport τ φ ZI).trans hsI
  have he := A.global_zeroPhase_quadrature τ Φ W hΦ hW
  rw [hWI,← A.restore_displacement i τ φ Z hs,← A.restore_displacement i τ φ ZI hsI,
    A.real_restored_metric i _ hdisp hsdisp,A.real_restored_metric i _ hdispI hsdispI] at he
  have hc :
      (fun y => fiberFromThree (RealModes.realMetricTensor (QuadraticMean.displacement τ φ Z)
        (planeCoordinateIsometry y))) +
      (fun y => fiberFromThree (RealModes.realMetricTensor (QuadraticMean.displacement τ φ ZI)
        (planeCoordinateIsometry y))) =
      (2 : ℝ) • (fun y => fiberFromThree (RealModes.phaseZeroTensor τ φ Z (planeCoordinateIsometry y))) := by
    funext y
    change fiberFromThree _ + fiberFromThree _ = (2 : ℝ) • fiberFromThree _
    rw [← map_add,← RealModes.phaseZeroTensor_quadrature
      (hφ.differentiable (by simp) _) (hZ.differentiable (by simp) _) τ,map_smul]
  rw [← A.bundleRestore_add,hc,A.bundleRestore_smul] at he
  funext p
  ext v w
  have hv := congrArg (fun T => T p v w) he
  change (2 : ℝ) * _ = 2 * _ at hv
  exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hv

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
