import OAI.Geometry.SurfaceImmersion.Correction.PolynomialValueBounds
import OAI.Geometry.SurfaceImmersion.Geometry.TensorRestoreFinite
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasFiniteCancellation
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricBounds

namespace OAI

/-! The actual globally restored polynomial perturbation of the metric,
with its exact first, second and higher-order variation decomposition. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinate_polynomial_taylor_identity {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) {G : Base → Space}
    {X : RealModes.RField 4} (hG : ContDiff ℝ ∞ G) (hX : ContDiff ℝ ∞ X) :
    coordinatePolynomialValue P ε (fun x => G x+X (planeCoordinateIsometry x)) 0-
      coordinatePolynomialValue P ε G 0 =
      coordinateRealLinearized P ε G X 0 + coordinateQuadraticPolynomial P ε G X 0 +
        coordinateTaylorRemainder P ε G X := by
  funext p k
  simp only [coordinateRealLinearized,coordinateQuadraticPolynomial,coordinatePolynomialValue,
    coordinateTaylorRemainder,linearized,Pi.add_apply,Pi.sub_apply,Expression.taylorRemainder]
  simp only [second_diagonal_eq_pair _ hG (hX.comp planeCoordinateIsometry.contDiff),
    mul_sub,Finset.sum_sub_distrib,Function.comp_apply]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance polynomialMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialMetricDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialMetricSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialMetricSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable {n : A.centers → ℕ}

def atlasPolynomialValue (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression)
    (ε : ℝ) (G : M → Space) : ∀ x : M, CovariantTwoTensor x :=
  A.tensorPlaneRestore (fun i => coordinatePolynomialValue (P i) ε (A.jetChartMap i G) 0)

def atlasPolynomialMetric (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression)
    (ε : ℝ) (G : M → Space) : ∀ x : M, CovariantTwoTensor x :=
  inducedTensor G+A.atlasPolynomialValue P ε G

def atlasPolynomialVariation (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression)
    (ε : ℝ) (G X : M → Space) : ∀ x : M, CovariantTwoTensor x :=
  A.tensorPlaneRestore (fun i => coordinateRealLinearized (P i) ε (A.jetChartMap i G)
    (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0)

def atlasPolynomialQuadratic (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression)
    (ε : ℝ) (G X : M → Space) : ∀ x : M, CovariantTwoTensor x :=
  A.tensorPlaneRestore (fun i => coordinateQuadraticPolynomial (P i) ε (A.jetChartMap i G)
    (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0)

def atlasPolynomialRemainder (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression)
    (ε : ℝ) (G X : M → Space) : ∀ x : M, CovariantTwoTensor x :=
  A.tensorPlaneRestore (fun i => coordinateTaylorRemainder (P i) ε (A.jetChartMap i G)
    (A.jetChartMap i X ∘ planeCoordinateIsometry.symm))

omit [CompactSpace M] in
lemma atlasPolynomialValue_symmetric
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε : ℝ) (G : M → Space) :
    ∀ x v w, A.atlasPolynomialValue P ε G x v w = A.atlasPolynomialValue P ε G x w v :=
  A.tensorPlaneRestore_symmetric _

omit [CompactSpace M] in
lemma atlasPolynomialMetric_symmetric
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε : ℝ) (G : M → Space) :
    ∀ x v w, A.atlasPolynomialMetric P ε G x v w = A.atlasPolynomialMetric P ε G x w v := by
  intro x v w
  change inducedTensor G x v w+A.atlasPolynomialValue P ε G x v w =
    inducedTensor G x w v+A.atlasPolynomialValue P ε G x w v
  rw [inducedTensor_symmetric G x v w,A.atlasPolynomialValue_symmetric P ε G x v w]

lemma atlasPolynomialValue_smooth
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {G : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (ε : ℝ) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.atlasPolynomialValue P ε G x)) :=
  A.tensorPlaneRestore_smooth (fun i => coordinatePolynomialValue_smooth (hP i)
    (A.jetChartMap_smooth i hG) ε)

lemma atlasPolynomialMetric_smooth
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {G : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (ε : ℝ) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.atlasPolynomialMetric P ε G x)) :=
  (A.inducedTensor_smooth hG).add_section (A.atlasPolynomialValue_smooth hP hG ε)

omit [CompactSpace M] in
lemma jetChartMap_add (i : A.centers) (G X : M → Space) :
    A.jetChartMap i (G+X) = A.jetChartMap i G+A.jetChartMap i X := by
  have h := A.vectorPlaneRead_add i G X
  funext x
  have hh := congrFun h (planeCoordinateIsometry x)
  change spaceCoordinates (A.vectorChartRead i (G+X) x) =
    spaceCoordinates (A.vectorChartRead i G x)+spaceCoordinates (A.vectorChartRead i X x)
  simpa only [vectorPlaneRead,Function.comp_apply,planeCoordinateIsometry.symm_apply_apply,
    Pi.add_apply,map_add] using congrArg spaceCoordinates hh

lemma atlas_polynomial_taylor_identity
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε : ℝ)
    {G X : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G)
    (hX : ContMDiff planeModel spaceModel ∞ X) :
    A.atlasPolynomialValue P ε (G+X)-A.atlasPolynomialValue P ε G =
      A.atlasPolynomialVariation P ε G X+A.atlasPolynomialQuadratic P ε G X+
        A.atlasPolynomialRemainder P ε G X := by
  unfold atlasPolynomialValue atlasPolynomialVariation atlasPolynomialQuadratic atlasPolynomialRemainder
  rw [← A.tensorPlaneRestore_sub,← A.tensorPlaneRestore_add,← A.tensorPlaneRestore_add]
  congr 1
  funext i
  simp only [Pi.sub_apply,Pi.add_apply]
  rw [A.jetChartMap_add]
  have hh := coordinate_polynomial_taylor_identity (P i) ε (A.jetChartMap_smooth i hG)
    ((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff)
  change coordinatePolynomialValue (P i) ε (fun x => A.jetChartMap i G x+A.jetChartMap i X x) 0-
    coordinatePolynomialValue (P i) ε (A.jetChartMap i G) 0 = _
  simpa only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply] using hh

lemma atlas_polynomial_metric_taylor_identity
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε : ℝ)
    {G X : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G)
    (hX : ContMDiff planeModel spaceModel ∞ X) :
    A.atlasPolynomialMetric P ε (G+X)-A.atlasPolynomialMetric P ε G =
      (linearMetricTensor G X+A.atlasPolynomialVariation P ε G X)+
      (inducedTensor X+A.atlasPolynomialQuadratic P ε G X)+
        A.atlasPolynomialRemainder P ε G X := by
  have hp := A.atlas_polynomial_taylor_identity P ε hG hX
  have hm := inducedTensor_add hG hX
  unfold atlasPolynomialMetric
  rw [hm]
  have hi : (inducedTensor G+linearMetricTensor G X+inducedTensor X+
      A.atlasPolynomialValue P ε (G+X))-(inducedTensor G+A.atlasPolynomialValue P ε G) =
      linearMetricTensor G X+inducedTensor X+
        (A.atlasPolynomialValue P ε (G+X)-A.atlasPolynomialValue P ε G) := by abel
  rw [hi,hp]
  abel

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
