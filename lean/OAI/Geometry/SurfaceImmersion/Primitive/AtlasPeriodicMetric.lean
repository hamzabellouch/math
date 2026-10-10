import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPeriodicAnsatz
import OAI.Geometry.SurfaceImmersion.Correction.RestoredLinearizedMetric
import OAI.Geometry.SurfaceImmersion.Correction.BundleSmoothingLinearity

namespace OAI

/-! The metric of the supported global periodic map is exactly the
restoration of the metric of its local periodic ansatz. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
local instance periodicMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance periodicMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance periodicMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance periodicMetricDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance periodicMetricSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance periodicMetricSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma restored_metric_increment (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (f : SmallModes.Base → Space)
    (hf : ContDiff ℝ ∞ f)
    (hsp : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    inducedTensor (F+restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry))-inducedTensor F =
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
        (RealModes.realMetricTensor (spaceCoordinates ∘ (A.vectorPlaneRead i F+f)) (planeCoordinateIsometry y)-
          RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (planeCoordinateIsometry y))) := by
  have hrest := restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    (hf.comp planeCoordinateIsometry.contDiff)
  rw [inducedTensor_add hF hrest]
  have he : (inducedTensor F+linearMetricTensor F (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry))+
      inducedTensor (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)))-inducedTensor F =
      linearMetricTensor F (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry))+
        inducedTensor (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) := by abel
  rw [he,A.restored_linearized_metric i hF f hf hsp,A.restored_metric_tensor i f hf hsp,
    ← A.bundleRestore_add]
  congr 1
  funext y
  have hcoord : spaceCoordinates ∘ (A.vectorPlaneRead i F+f) =
      (fun x => spaceCoordinates (A.vectorPlaneRead i F x)+spaceCoordinates (f x)) := by
    funext x
    exact map_add spaceCoordinates _ _
  rw [hcoord]
  have hadd := RealModes.realMetricTensor_add
    ((spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)).differentiable
      (by simp) (planeCoordinateIsometry y))
    ((spaceCoordinates.contDiff.comp hf).differentiable (by simp) (planeCoordinateIsometry y))
  change RealModes.realMetricTensor
    (fun x => spaceCoordinates (A.vectorPlaneRead i F x)+spaceCoordinates (f x))
    (planeCoordinateIsometry y) = _ at hadd
  rw [hadd]
  simp only [Pi.add_apply]
  rw [← map_add]
  congr 1
  abel

lemma periodicAtlasAnsatz_metric (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsClosed K) (hKO : K ⊆ O)
    (hKA : K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    inducedTensor (A.periodicAtlasAnsatz i F U ℓ L z)-inducedTensor F =
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
        (RealModes.realMetricTensor
          (spaceCoordinates ∘ finiteAnsatz (A.vectorChartRead i F) U ℓ L z ∘ planeCoordinateIsometry.symm)
          (planeCoordinateIsometry y)-
          RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (planeCoordinateIsometry y))) := by
  let H := finiteAnsatz (A.vectorChartRead i F) U ℓ L z-A.vectorChartRead i F
  have hH := (finiteAnsatz_smooth_global (A.vectorChartRead_smooth i hF) U hK hKO
    (fun j x _ hx => hzero j x hx) ℓ L z).sub (A.vectorChartRead_smooth i hF)
  have hs := (finiteAnsatz_tsupport_sub (A.vectorChartRead i F) U hK hzero ℓ L z).trans hKA
  have hsp : tsupport (H ∘ planeCoordinateIsometry.symm) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    intro x hx
    have hh := hs (tsupport_comp_preimage H planeCoordinateIsometry.symm
      planeCoordinateIsometry.symm.continuous hx)
    exact ⟨planeCoordinateIsometry.symm x,hh,planeCoordinateIsometry.apply_symm_apply x⟩
  have hr := A.restored_metric_increment i hF (H ∘ planeCoordinateIsometry.symm)
    (hH.comp planeCoordinateIsometry.symm.contDiff) hsp
  have he : (H ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry = H := by
    funext x
    simp
  have hb : A.vectorPlaneRead i F+H ∘ planeCoordinateIsometry.symm =
      finiteAnsatz (A.vectorChartRead i F) U ℓ L z ∘ planeCoordinateIsometry.symm := by
    funext x
    change A.vectorChartRead i F (planeCoordinateIsometry.symm x)+
      (finiteAnsatz (A.vectorChartRead i F) U ℓ L z (planeCoordinateIsometry.symm x)-
        A.vectorChartRead i F (planeCoordinateIsometry.symm x)) = _
    simp only [Function.comp_apply]
    abel
  rw [he,hb] at hr
  exact hr

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
