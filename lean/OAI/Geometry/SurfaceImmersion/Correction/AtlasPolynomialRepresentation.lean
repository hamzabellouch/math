import OAI.Geometry.SurfaceImmersion.Correction.AtlasRestoredPolynomialRepresentation
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialFiniteAssembly
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
local instance polyRepFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polyRepFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polyRepDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polyRepDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polyRepSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polyRepSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma tensorChartRead_sum {ι : Type*} [Fintype ι] (i : A.centers)
    (u : ι → ∀ p : M, CovariantTwoTensor p) :
    A.tensorChartRead i (∑ k, u k) = ∑ k, A.tensorChartRead i (u k) := by
  classical
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_mem hx,bundleComponent,Finset.sum_apply,map_sum,Finset.smul_sum]
  · simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_notMem hx,map_zero,Finset.sum_apply,Finset.sum_const_zero]

/-- Every correction chart reads the globally restored polynomial as a
single finite polynomial in that chart's actual localized map. -/
theorem atlas_polynomial_representation {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) (i : A.centers) :
    ∃ Q : Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ k r, (Q k r).SmoothCoeffs univ) ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ∀ (x : Base), A.chartWeight i x ≠ 0 → ∀ ε : ℝ,
          coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (JetPolynomial.planeCoordinateIsometry x) =
            A.tensorChartRead i (A.atlasPolynomialValue P ε F) x := by
  classical
  choose Q hQ hvalue using fun j : A.centers =>
    A.restored_polynomial_representation i j (P j) (hP j)
  refine ⟨sumTensorPolynomials Q,sumTensorPolynomials_smooth hQ,?_⟩
  intro F hF x hx ε
  have hrestore : A.atlasPolynomialValue P ε F =
      ∑ j : A.centers, A.bundleRestore A.tensorTriv j
        (fun y => fiberFromThree (coordinatePolynomialValue (P j) ε (A.jetChartMap j F) 0
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
