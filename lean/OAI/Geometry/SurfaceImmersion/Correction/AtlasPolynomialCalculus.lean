import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialMetric
import OAI.Geometry.SurfaceImmersion.Correction.CoordinatePolynomialCalculus
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasTensorDerivatives

namespace OAI

/-! First and second derivatives of the globally restored polynomial
are the operators used in its exact Taylor identity. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance polynomialDerivativeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialDerivativeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialDerivativeDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialDerivativeDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialDerivativeSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialDerivativeSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma jetChartMap_affine (i : A.centers) (F X : M → Space) (s : ℝ) :
    A.jetChartMap i (F+s • X) = A.jetChartMap i F+s • A.jetChartMap i X := by
  rw [A.jetChartMap_add]
  congr 1
  funext x
  change spaceCoordinates (localize (i : M) (A.outer i) (s • X) x) =
    s • spaceCoordinates (localize (i : M) (A.outer i) X x)
  rw [localize_smul]
  exact map_smul spaceCoordinates s _

lemma atlasPolynomialValue_hasDerivAt {n : A.centers → ℕ}
    {P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) (ε : ℝ)
    {F X : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hX : ContMDiff planeModel spaceModel ∞ X) (p : M) :
    HasDerivAt (fun s : ℝ => A.atlasPolynomialValue P ε (F+s • X) p)
      (A.atlasPolynomialVariation P ε F X p) 0 := by
  unfold atlasPolynomialValue atlasPolynomialVariation
  apply A.tensorPlaneRestore_hasDerivAt
  intro i
  simp only [A.jetChartMap_affine]
  exact coordinatePolynomialValue_hasDerivAt (hP i) ε 0
    (A.jetChartMap_smooth i hF) (A.jetChartMap_smooth i hX) (chart (i : M) p)

lemma atlasPolynomialVariation_hasDerivAt {n : A.centers → ℕ}
    {P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) (ε : ℝ)
    {F X : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hX : ContMDiff planeModel spaceModel ∞ X) (p : M) :
    HasDerivAt (fun s : ℝ => A.atlasPolynomialVariation P ε (F+s • X) X p)
      ((2 : ℝ) • A.atlasPolynomialQuadratic P ε F X p) 0 := by
  have hd := A.tensorPlaneRestore_hasDerivAt
    (f := fun s i => coordinateRealLinearized (P i) ε
      (A.jetChartMap i F+s • A.jetChartMap i X)
      (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0)
    (f' := fun i => (2 : ℝ) • coordinateQuadraticPolynomial (P i) ε (A.jetChartMap i F)
      (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0) p (fun i =>
    coordinateRealLinearized_hasDerivAt (hP i) ε 0
      (A.jetChartMap_smooth i hF) (A.jetChartMap_smooth i hX) (chart (i : M) p))
  change HasDerivAt _ (A.tensorPlaneRestore ((2 : ℝ) • fun i =>
    coordinateQuadraticPolynomial (P i) ε (A.jetChartMap i F)
      (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0) p) 0 at hd
  rw [A.tensorPlaneRestore_smul] at hd
  simpa only [atlasPolynomialVariation,atlasPolynomialQuadratic,A.jetChartMap_affine,
    Pi.smul_apply] using hd

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
