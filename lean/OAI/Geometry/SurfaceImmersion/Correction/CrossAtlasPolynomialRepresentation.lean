import OAI.Geometry.SurfaceImmersion.Correction.CrossAtlasRestoredPolynomial
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialRepresentation
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialMetric

namespace OAI

/-! Constructed coordinate representatives of the same global polynomial
tensor. These are derived from the actual read/restore maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
local instance crossPolyRepFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance crossPolyRepFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance crossPolyRepDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance crossPolyRepDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance crossPolyRepSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossPolyRepSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

/-- Every correction chart reads the globally restored polynomial as a
single finite polynomial in that chart's actual localized map. -/
theorem cross_atlas_polynomial_representation {n : B.centers → ℕ}
    (P : ∀ j : B.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) (i : A.centers) :
    ∃ Q : Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ k r, (Q k r).SmoothCoeffs univ) ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ∀ (x : Base), A.chartWeight i x ≠ 0 → ∀ ε : ℝ,
          coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (JetPolynomial.planeCoordinateIsometry x) =
            A.tensorChartRead i (B.atlasPolynomialValue P ε F) x := by
  classical
  choose Q hQ hvalue using fun j : B.centers =>
    A.cross_restored_polynomial_representation B i j (P j) (hP j)
  refine ⟨sumTensorPolynomials Q,sumTensorPolynomials_smooth hQ,?_⟩
  intro F hF x hx ε
  have hrestore : B.atlasPolynomialValue P ε F =
      ∑ j : B.centers, B.bundleRestore B.tensorTriv j
        (fun y => fiberFromThree (coordinatePolynomialValue (P j) ε (B.jetChartMap j F) 0
          (JetPolynomial.planeCoordinateIsometry y))) := by
    funext p
    simp only [atlasPolynomialValue,tensorPlaneRestore,Finset.sum_apply]
  rw [sumTensorPolynomials_value,hrestore,A.tensorChartRead_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact hvalue j F hF x hx ε 0

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
