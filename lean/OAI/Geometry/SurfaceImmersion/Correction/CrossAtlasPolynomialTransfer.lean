import OAI.Geometry.SurfaceImmersion.Correction.CrossAtlasPolynomialRepresentation
import OAI.Geometry.SurfaceImmersion.Atlas.TensorReadReconstruction

namespace OAI

/-! A finite polynomial mean tensor is independent of the correction atlas. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression planeCoordinateIsometry)
open JetPolynomial.Perturbation
local instance polyTransferFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polyTransferFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polyTransferDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polyTransferDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polyTransferSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polyTransferSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem cross_atlas_polynomial_transfer {n : B.centers → ℕ}
    (P : ∀ j : B.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) :
    ∃ Q : A.centers → Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ i k r, (Q i k r).SmoothCoeffs univ) ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F → ∀ ε : ℝ,
        A.atlasPolynomialMetric Q ε F = B.atlasPolynomialMetric P ε F := by
  classical
  choose R hR hrep using fun i : A.centers => A.cross_atlas_polynomial_representation B P hP i
  let L : A.centers → Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor :=
    fun i x => (A.chartWeight i x)^2 • ContinuousLinearMap.id ℝ PhaseMean.Tensor
  have hL (i : A.centers) : ContDiff ℝ ∞ (L i) := (A.chartWeight_smooth i).pow 2 |>.smul contDiff_const
  let Q := fun i => mapTensorPolynomial (L i) (R i)
  refine ⟨Q,fun i => mapTensorPolynomial_smooth (hL i) (hR i),?_⟩
  intro F hF ε
  have hvalue : A.atlasPolynomialValue Q ε F = B.atlasPolynomialValue P ε F := by
    have heq : (fun i => coordinatePolynomialValue (Q i) ε (A.jetChartMap i F) 0) =
        (fun i x => (A.planeWeight i x)^2 • A.tensorPlaneRead i (B.atlasPolynomialValue P ε F) x) := by
      funext i x
      let y := planeCoordinateIsometry.symm x
      have hxy : planeCoordinateIsometry y = x := planeCoordinateIsometry.apply_symm_apply x
      rw [← hxy,mapTensorPolynomial_eval]
      change (A.chartWeight i y)^2 • coordinatePolynomialValue (R i) ε (A.jetChartMap i F) 0
          (planeCoordinateIsometry y) =
        (A.planeWeight i (planeCoordinateIsometry y))^2 •
          A.tensorPlaneRead i (B.atlasPolynomialValue P ε F) (planeCoordinateIsometry y)
      simp only [planeWeight,tensorPlaneRead,Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
      by_cases hy : A.chartWeight i y = 0
      · simp only [hy,zero_pow (by decide : 2 ≠ 0),zero_smul]
      · rw [hrep i F hF y hy ε]
    change A.tensorPlaneRestore _ = B.atlasPolynomialValue P ε F
    rw [heq,A.tensorPlaneRestore_partition_read _ (B.atlasPolynomialValue_symmetric P ε F)]
  exact congrArg (fun T => inducedTensor F+T) hvalue

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
