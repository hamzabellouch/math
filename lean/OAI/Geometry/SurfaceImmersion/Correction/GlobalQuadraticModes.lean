import OAI.Geometry.SurfaceImmersion.Atlas.MetricChartReconstruction
import OAI.Geometry.SurfaceImmersion.Correction.GlobalModeDifferential
import OAI.Geometry.SurfaceImmersion.Correction.QuadratureMean

namespace OAI

/-! Global quadratic phase expansion, retaining all cross-chart interactions. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance globalModeMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance globalModeMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance globalModeMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance globalModeMetricDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance globalModeMetricSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance globalModeMetricSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem global_mode_metric (τ : ℝ) (φ : M → ℝ) (Z : M → Fin 4 → ℂ)
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ Z) :
    inducedTensor (spaceCoordinates.symm ∘ surfaceMode τ φ Z) =
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        RealModes.realMetricTensor (QuadraticMean.displacement τ
          (A.vectorPlaneRead i φ) (A.vectorPlaneRead i Z)) x) := by
  have he (i : A.centers) :
      spaceCoordinates ∘ A.vectorPlaneRead i (spaceCoordinates.symm ∘ surfaceMode τ φ Z) =
        A.vectorPlaneRead i (surfaceMode τ φ Z) := by
    have hr : A.vectorPlaneRead i (spaceCoordinates.symm ∘ surfaceMode τ φ Z) =
        spaceCoordinates.symm ∘ A.vectorPlaneRead i (surfaceMode τ φ Z) :=
      A.vectorPlaneRead_clm i spaceCoordinates.symm.toContinuousLinearMap (surfaceMode τ φ Z)
    rw [hr]
    funext x
    exact spaceCoordinates.apply_symm_apply _
  rw [← A.metric_from_chart_reads
    (spaceCoordinates.symm.contDiff.contMDiff.comp (surfaceMode_smooth τ hφ hZ))]
  simp_rw [he]
  congr 1
  funext i x
  by_cases hw : A.planeWeight i x = 0
  · simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_smul]
  · have hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
      (A.supportedPlaneWeight i).tsupport_subset (subset_tsupport (A.planeWeight i) hw)
    have hd := A.vectorPlaneRead_mode_fderiv i τ hφ hZ hx
    congr 1
    ext k
    simp only [RealModes.realMetricTensor_apply,RealModes.realMetric,SmallModes.coordDeriv,hd]

theorem global_zeroPhase_quadrature (τ : ℝ) (φ : M → ℝ) (Z : M → Fin 4 → ℂ)
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ Z) :
    (2 : ℝ) • A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
      RealModes.phaseZeroTensor τ (A.vectorPlaneRead i φ) (A.vectorPlaneRead i Z) x) =
      inducedTensor (spaceCoordinates.symm ∘ surfaceMode τ φ Z) +
      inducedTensor (spaceCoordinates.symm ∘ surfaceMode τ φ (fun p => Complex.I • Z p)) := by
  have hIc : ContDiff ℝ ∞ (fun z : Fin 4 → ℂ => Complex.I • z) :=
    (contDiff_const (c := Complex.I)).smul contDiff_id
  have hi : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (fun p => Complex.I • Z p) :=
    hIc.contMDiff.comp hZ
  rw [A.global_mode_metric τ φ Z hφ hZ,A.global_mode_metric τ φ _ hφ hi,
    ← A.tensorPlaneRestore_add,← A.tensorPlaneRestore_smul]
  congr 1
  funext i x
  simp only [Pi.smul_apply,Pi.add_apply,A.vectorPlaneRead_const_smul]
  rw [smul_comm (2 : ℝ) ((A.planeWeight i x)^2),
    RealModes.phaseZeroTensor_quadrature
      ((A.vectorPlaneRead_smooth i hφ).differentiable (by simp) x)
      ((A.vectorPlaneRead_smooth i hZ).differentiable (by simp) x),smul_add]

theorem global_modes_metric {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j)) :
    inducedTensor (spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)) =
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        RealModes.zeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
          (fun j => A.vectorPlaneRead i (Z j)) x) +
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        RealModes.nonzeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
          (fun j => A.vectorPlaneRead i (Z j)) x) := by
  classical
  let U : M → RealModes.RVec 4 := ∑ j, surfaceMode τ (φ j) (Z j)
  have hU : ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ U := by
    have hh := ContMDiff.sum (t := Finset.univ) (fun j _ => surfaceMode_smooth τ (hφ j) (hZ j))
    convert hh using 1
    funext x
    simp only [U,Finset.sum_apply]
  have he (i : A.centers) :
      spaceCoordinates ∘ A.vectorPlaneRead i (spaceCoordinates.symm ∘ U) = A.vectorPlaneRead i U := by
    have hr : A.vectorPlaneRead i (spaceCoordinates.symm ∘ U) =
        spaceCoordinates.symm ∘ A.vectorPlaneRead i U :=
      A.vectorPlaneRead_clm i spaceCoordinates.symm.toContinuousLinearMap U
    rw [hr]
    funext x
    exact spaceCoordinates.apply_symm_apply _
  rw [← A.metric_from_chart_reads (spaceCoordinates.symm.contDiff.contMDiff.comp hU)]
  simp_rw [he]
  rw [← A.tensorPlaneRestore_add]
  congr 1
  funext i x
  by_cases hw : A.planeWeight i x = 0
  · simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_smul,Pi.add_apply,zero_add]
  · have hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
      (A.supportedPlaneWeight i).tsupport_subset (subset_tsupport (A.planeWeight i) hw)
    rw [A.vectorPlaneRead_modes_metric i τ φ Z hφ hZ hx,smul_add]
    rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
