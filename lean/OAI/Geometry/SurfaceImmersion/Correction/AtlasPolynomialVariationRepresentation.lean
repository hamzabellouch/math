import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialRepresentation
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialCalculus
import OAI.Geometry.SurfaceImmersion.Geometry.InitialInputBounds

namespace OAI

/-! The local representatives differentiate to the same first and second
variations as the global polynomial tensor. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance variationRepFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance variationRepFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance variationRepDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance variationRepDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance variationRepSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance variationRepSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma tensorChartRead_smul (i : A.centers) (c : ℝ) (u : ∀ p : M, CovariantTwoTensor p) :
    A.tensorChartRead i (c • u) = c • A.tensorChartRead i u := by
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_mem hx,bundleComponent,Pi.smul_apply,map_smul]
    rw [smul_comm]
  · simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_notMem hx,map_zero,Pi.smul_apply,smul_zero]

lemma polynomial_first_of_representation {n : A.centers → ℕ} {m : ℕ}
    {P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (i : A.centers) {Q : Fin 3 → Fin m → Expression}
    (hQ : ∀ k l, (Q k l).SmoothCoeffs univ)
    (x : Base)
    (hrep : ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F → ∀ ε : ℝ,
      coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (planeCoordinateIsometry x) =
        A.tensorChartRead i (A.atlasPolynomialValue P ε F) x)
    {F X : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hX : ContMDiff planeModel spaceModel ∞ X) (ε : ℝ) :
    coordinateRealLinearized Q ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
      A.tensorChartRead i (A.atlasPolynomialVariation P ε F X) x := by
  have hl := coordinatePolynomialValue_hasDerivAt hQ ε 0
    (A.jetChartMap_smooth i hF) (A.jetChartMap_smooth i hX) x
  have hr := A.tensorChartRead_hasDerivAt i x
    (A.atlasPolynomialValue_hasDerivAt hP ε hF hX ((chart (i : M)).symm x))
  have he : (fun s : ℝ => coordinatePolynomialValue Q ε
      (A.jetChartMap i F+s • A.jetChartMap i X) 0 (planeCoordinateIsometry x)) =
      (fun s : ℝ => A.tensorChartRead i (A.atlasPolynomialValue P ε (F+s • X)) x) := by
    funext s
    rw [← A.jetChartMap_affine]
    exact hrep (F+s • X) (hF.add (space_smul_contMDiff hX s)) ε
  rw [he] at hl
  exact hl.unique hr

lemma polynomial_quadratic_of_representation {n : A.centers → ℕ} {m : ℕ}
    {P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (i : A.centers) {Q : Fin 3 → Fin m → Expression}
    (hQ : ∀ k l, (Q k l).SmoothCoeffs univ)
    (x : Base)
    (hrep : ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F → ∀ ε : ℝ,
      coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (planeCoordinateIsometry x) =
        A.tensorChartRead i (A.atlasPolynomialValue P ε F) x)
    {F X : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hX : ContMDiff planeModel spaceModel ∞ X) (ε : ℝ) :
    coordinateQuadraticPolynomial Q ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
      A.tensorChartRead i (A.atlasPolynomialQuadratic P ε F X) x := by
  have hl := coordinateRealLinearized_hasDerivAt hQ ε 0
    (A.jetChartMap_smooth i hF) (A.jetChartMap_smooth i hX) x
  have hr := A.tensorChartRead_hasDerivAt
    (f := fun s => A.atlasPolynomialVariation P ε (F+s • X) X)
    (f' := (2 : ℝ) • A.atlasPolynomialQuadratic P ε F X) i x
    (A.atlasPolynomialVariation_hasDerivAt hP ε hF hX ((chart (i : M)).symm x))
  have he : (fun s : ℝ => coordinateRealLinearized Q ε
      (A.jetChartMap i F+s • A.jetChartMap i X)
      (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x)) =
      (fun s : ℝ => A.tensorChartRead i (A.atlasPolynomialVariation P ε (F+s • X) X) x) := by
    funext s
    rw [← A.jetChartMap_affine]
    exact A.polynomial_first_of_representation hP i hQ x hrep
      (hF.add (space_smul_contMDiff hX s)) hX ε
  rw [he] at hl
  have hh := hl.unique hr
  have hs := congrFun (A.tensorChartRead_smul i (2 : ℝ)
    (A.atlasPolynomialQuadratic P ε F X)) x
  rw [hs] at hh
  have hc := congrArg (fun t : Tensor => (1/2 : ℝ) • t) hh
  simpa only [Pi.smul_apply,smul_smul,show (1/2 : ℝ)*2 = 1 by norm_num,one_smul] using hc

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
