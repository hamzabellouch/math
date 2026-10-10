import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPeriodicMetric
import OAI.Geometry.SurfaceImmersion.Geometry.LocalSingleTensorRestoreBound
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPrimitivePolynomial

namespace OAI

/-! Exact decomposition of a global primitive's metric defect into the
solved polynomial mean error and the finite periodic remainder. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
local instance supportedLocalDefectFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance supportedLocalDefectFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance supportedLocalDefectDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance supportedLocalDefectDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance supportedLocalDefectSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance supportedLocalDefectSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Any supported local map, including a nonlinear phase ansatz, has the
same exact global defect decomposition. -/
lemma supported_local_metric_defect (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (f : JetPolynomial.Base → Space)
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    {n : ℕ} (P : Fin 3 → Fin n → Expression) (z : ℝ)
    (γ : ∀ x : M, CovariantTwoTensor x) (H : SmallModes.Base → PhaseMean.Tensor) :
    inducedTensor (F + restore (i : M) (A.outer i) f) -
        (γ + A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (H (planeCoordinateIsometry y)))) =
      (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i P) z F - γ) +
        A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
          (RealModes.realMetricTensor
              (spaceCoordinates ∘ (A.vectorChartRead i F + f) ∘ planeCoordinateIsometry.symm)
                (planeCoordinateIsometry y) -
            coordinateMetricMap P z (A.jetChartMap i F) (planeCoordinateIsometry y) -
            H (planeCoordinateIsometry y))) := by
  have hsp : tsupport (f ∘ planeCoordinateIsometry.symm) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    intro x hx
    have hh := hs (tsupport_comp_preimage f planeCoordinateIsometry.symm
      planeCoordinateIsometry.symm.continuous hx)
    exact ⟨planeCoordinateIsometry.symm x,hh,planeCoordinateIsometry.apply_symm_apply x⟩
  have hm := A.restored_metric_increment i hF (f ∘ planeCoordinateIsometry.symm)
    (hf.comp planeCoordinateIsometry.symm.contDiff) hsp
  have he : (f ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry = f := by
    funext x
    simp
  rw [he] at hm
  have hp := A.atlasPolynomialValue_primitive i P z F
  have hmetric : inducedTensor (F+restore (i : M) (A.outer i) f) = inducedTensor F +
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
        (RealModes.realMetricTensor
            (spaceCoordinates ∘ (A.vectorChartRead i F + f) ∘ planeCoordinateIsometry.symm)
              (planeCoordinateIsometry y) -
          RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
            (planeCoordinateIsometry y))) := by
    have heq : spaceCoordinates ∘ (A.vectorPlaneRead i F + f ∘ planeCoordinateIsometry.symm) =
        spaceCoordinates ∘ (A.vectorChartRead i F + f) ∘ planeCoordinateIsometry.symm := rfl
    rw [heq] at hm
    rw [← hm]
    abel
  rw [hmetric,atlasPolynomialMetric,hp]
  funext p
  simp only [coordinateMetricMap,Pi.add_apply,Pi.sub_apply,bundleRestore,map_sub,map_add,smul_sub,smul_add]
  have heq : A.jetChartMap i F ∘ planeCoordinateIsometry.symm =
      spaceCoordinates ∘ A.vectorPlaneRead i F := rfl
  rw [heq]
  abel

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
