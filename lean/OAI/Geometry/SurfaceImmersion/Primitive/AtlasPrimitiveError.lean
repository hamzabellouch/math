import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPeriodicMetric
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPrimitivePolynomial

namespace OAI

/-! Exact decomposition of a global primitive's metric defect into the
solved polynomial mean error and the finite periodic remainder. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
local instance primitiveErrorFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance primitiveErrorFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance primitiveErrorDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance primitiveErrorDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance primitiveErrorSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance primitiveErrorSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- All terms refer to the same local ansatz and its actual global extension. -/
lemma periodicAtlasAnsatz_defect (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsClosed K) (hKO : K ⊆ O)
    (hKA : K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (γ : ∀ x : M, CovariantTwoTensor x) (H : SmallModes.Base → PhaseMean.Tensor) :
    inducedTensor (A.periodicAtlasAnsatz i F U ℓ L z)-
        (γ+A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (H (planeCoordinateIsometry y)))) =
      (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i P) z F-γ)+
        A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
          (RealModes.realMetricTensor
            (spaceCoordinates ∘ finiteAnsatz (A.vectorChartRead i F) U ℓ L z ∘ planeCoordinateIsometry.symm)
              (planeCoordinateIsometry y)-
            RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (planeCoordinateIsometry y)-
            coordinatePolynomialValue P z (A.jetChartMap i F) 0 (planeCoordinateIsometry y)-
            H (planeCoordinateIsometry y))) := by
  have hm := A.periodicAtlasAnsatz_metric i hF U hK hKO hKA hzero ℓ L z
  have hp := A.atlasPolynomialValue_primitive i P z F
  have he : inducedTensor (A.periodicAtlasAnsatz i F U ℓ L z) = inducedTensor F+
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
        (RealModes.realMetricTensor
          (spaceCoordinates ∘ finiteAnsatz (A.vectorChartRead i F) U ℓ L z ∘ planeCoordinateIsometry.symm)
            (planeCoordinateIsometry y)-
          RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (planeCoordinateIsometry y))) := by
    rw [← hm]
    abel
  rw [he,atlasPolynomialMetric,hp]
  funext p
  simp only [Pi.add_apply,Pi.sub_apply,bundleRestore,map_sub,smul_sub]
  abel

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
