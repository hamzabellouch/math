import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialMetric
import OAI.Geometry.SurfaceImmersion.Geometry.PerturbedIncrementEstimate

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance polynomialSmoothFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialSmoothFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialSmoothDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialSmoothDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialSmoothSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialSmoothSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)




lemma atlasPolynomialVariation_smooth {n : A.centers → ℕ}
    {P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {F X : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hX : ContMDiff planeModel spaceModel ∞ X)
    (ε : ℝ) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.atlasPolynomialVariation P ε F X p)) := by
  apply A.tensorPlaneRestore_smooth
  intro i
  apply contDiff_pi.mpr
  intro k
  change ContDiff ℝ ∞ (fun p => ∑ l, ε^(l.val+1) *
    (P i k l).variation (A.jetChartMap i F)
      ((A.jetChartMap i X ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry)
      (planeCoordinateIsometry.symm p,0))
  apply ContDiff.sum
  intro l _
  apply contDiff_const.mul
  have hs := (P i k l).variation_smooth (U := univ) isOpen_univ
    (A.jetChartMap_smooth i hF)
    (((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff).comp
      planeCoordinateIsometry.contDiff) (fun _ _ => mem_univ _) (hP i k l)
  have hs' : ContDiff ℝ ∞ ((P i k l).variation (A.jetChartMap i F)
      ((A.jetChartMap i X ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry)) := by
    apply contDiffOn_univ.mp
    simpa only [univ_prod_univ] using hs
  exact hs'.comp (planeCoordinateIsometry.symm.contDiff.prodMk contDiff_const)

lemma atlasPolynomialQuadratic_smooth {n : A.centers → ℕ}
    {P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {F X : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hX : ContMDiff planeModel spaceModel ∞ X)
    (ε : ℝ) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.atlasPolynomialQuadratic P ε F X p)) :=
  A.tensorPlaneRestore_smooth (fun i => coordinateQuadraticPolynomial_smooth (hP i)
    (A.jetChartMap_smooth i hF)
    ((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff) ε 0)

lemma atlasPolynomialRemainder_smooth {n : A.centers → ℕ}
    {P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {F X : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hX : ContMDiff planeModel spaceModel ∞ X)
    (ε : ℝ) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.atlasPolynomialRemainder P ε F X p)) :=
  A.tensorPlaneRestore_smooth (fun i =>
    (tensorTaylorRemainder_smooth (hP i) (A.jetChartMap_smooth i hF)
      (((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff).comp
        planeCoordinateIsometry.contDiff) ε 0).comp planeCoordinateIsometry.symm.contDiff)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
