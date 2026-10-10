import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialVariationRepresentation
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricRead

namespace OAI

/-! A single local polynomial models the global perturbation, with its
first and second variations, on the entire compact chart support. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance localModelFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance localModelFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance localModelDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance localModelDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance localModelSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance localModelSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_polynomial_representation_on_support {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) (i : A.centers) :
    ∃ Q : Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ k r, (Q k r).SmoothCoeffs univ) ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ∀ x ∈ (A.chartWeightCompact i : Set Base), ∀ ε : ℝ,
          coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (planeCoordinateIsometry x) =
            A.tensorChartRead i (A.atlasPolynomialValue P ε F) x := by
  obtain ⟨Q,hQ,hrep⟩ := A.atlas_polynomial_representation P hP i
  refine ⟨Q,hQ,?_⟩
  intro F hF x hx ε
  have hc := isClosed_eq
    ((coordinatePolynomialValue_smooth hQ (A.jetChartMap_smooth i hF) ε).continuous.comp
      planeCoordinateIsometry.continuous)
    (A.tensorChartRead_smooth i (A.atlasPolynomialValue_smooth hP hF ε)).continuous
  have hd : Function.support (A.chartWeight i) ⊆
      {x | coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (planeCoordinateIsometry x) =
        A.tensorChartRead i (A.atlasPolynomialValue P ε F) x} :=
    fun y hy => hrep F hF y hy ε
  exact closure_minimal hd hc (by rwa [← A.chartWeight_tsupport i] at hx)

theorem atlas_polynomial_local_model {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) (i : A.centers) :
    ∃ Q : Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ k r, (Q k r).SmoothCoeffs univ) ∧
      (∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ∀ x ∈ (A.chartWeightCompact i : Set Base), ∀ ε : ℝ,
          coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (planeCoordinateIsometry x) =
            A.tensorChartRead i (A.atlasPolynomialValue P ε F) x) ∧
      (∀ (F X : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ContMDiff planeModel spaceModel ∞ X →
        ∀ x ∈ (A.chartWeightCompact i : Set Base), ∀ ε : ℝ,
          coordinateRealLinearized Q ε (A.jetChartMap i F)
              (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
            A.tensorChartRead i (A.atlasPolynomialVariation P ε F X) x) ∧
      (∀ (F X : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ContMDiff planeModel spaceModel ∞ X →
        ∀ x ∈ (A.chartWeightCompact i : Set Base), ∀ ε : ℝ,
          coordinateQuadraticPolynomial Q ε (A.jetChartMap i F)
              (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
            A.tensorChartRead i (A.atlasPolynomialQuadratic P ε F X) x) := by
  obtain ⟨Q,hQ,hvalue⟩ := A.atlas_polynomial_representation_on_support P hP i
  refine ⟨Q,hQ,hvalue,?_,?_⟩
  · intro F X hF hX x hx ε
    exact A.polynomial_first_of_representation hP i hQ x
      (fun G hG ε => hvalue G hG x hx ε) hF hX ε
  · intro F X hF hX x hx ε
    exact A.polynomial_quadratic_of_representation hP i hQ x
      (fun G hG ε => hvalue G hG x hx ε) hF hX ε

/-- The same local polynomials represent the global quadratic variation. -/
def PolynomialQuadraticRepresentation {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression) : Prop :=
  ∀ (F X : M → Space), ContMDiff planeModel spaceModel ∞ F →
    ContMDiff planeModel spaceModel ∞ X → ∀ i : A.centers,
      ∀ x ∈ (A.chartWeightCompact i : Set Base), ∀ ε : ℝ,
        coordinateQuadraticPolynomial (Q i) ε (A.jetChartMap i F)
            (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
          A.tensorChartRead i (A.atlasPolynomialQuadratic P ε F X) x

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
