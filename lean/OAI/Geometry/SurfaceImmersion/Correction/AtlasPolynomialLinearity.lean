import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialSupport

namespace OAI

/-! Finite linearity in the direction of the actual global polynomial. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateRealLinearized_add {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (ε : ℝ) (G : Base → Space) {X Y : RealModes.RField 4}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) (t : ℝ) :
    coordinateRealLinearized P ε G (X+Y) t =
      coordinateRealLinearized P ε G X t+coordinateRealLinearized P ε G Y t := by
  funext p k
  change linearized (P k) ε G (fun x => X (planeCoordinateIsometry x)+Y (planeCoordinateIsometry x))
    t (planeCoordinateIsometry.symm p) = _
  exact linearized_add (P k) ε G (hX.comp planeCoordinateIsometry.contDiff)
    (hY.comp planeCoordinateIsometry.contDiff) t (planeCoordinateIsometry.symm p)

end ClosedSurfaceR4.JetPolynomial.Perturbation

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance polynomialLinearFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialLinearFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialLinearDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialLinearDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialLinearSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialLinearSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma atlasPolynomialVariation_add {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression) (ε : ℝ) (F : M → Space)
    {X Y : M → Space} (hX : ContMDiff planeModel spaceModel ∞ X)
    (hY : ContMDiff planeModel spaceModel ∞ Y) :
    A.atlasPolynomialVariation P ε F (X+Y) =
      A.atlasPolynomialVariation P ε F X+A.atlasPolynomialVariation P ε F Y := by
  unfold atlasPolynomialVariation
  rw [← A.tensorPlaneRestore_add]
  congr 1
  funext i
  have he : A.jetChartMap i (X+Y) ∘ planeCoordinateIsometry.symm =
      (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)+
        (A.jetChartMap i Y ∘ planeCoordinateIsometry.symm) := by
    rw [A.jetChartMap_add]
    rfl
  rw [he,coordinateRealLinearized_add (P i) ε _
    ((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff)
    ((A.jetChartMap_smooth i hY).comp planeCoordinateIsometry.symm.contDiff)]
  rfl

omit [CompactSpace M] in
lemma atlasPolynomialVariation_zero {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression) (ε : ℝ) (F : M → Space) :
    A.atlasPolynomialVariation P ε F 0 = 0 := by
  funext p
  exact A.atlasPolynomialVariation_zero_of_notMem P ε F 0 (by simp)

lemma atlasPolynomialVariation_sum {n : A.centers → ℕ} {ι : Type*}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression) (ε : ℝ) (F : M → Space)
    (S : Finset ι) (X : ι → M → Space) (hX : ∀ i, ContMDiff planeModel spaceModel ∞ (X i)) :
    A.atlasPolynomialVariation P ε F (∑ i ∈ S, X i) =
      ∑ i ∈ S, A.atlasPolynomialVariation P ε F (X i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,A.atlasPolynomialVariation_zero]
  | @insert i S hi ih =>
    have hs : ContMDiff planeModel spaceModel ∞ (∑ j ∈ S, X j) := by
      convert ContMDiff.sum (t := S) (fun j _ => hX j) using 1
      funext p
      simp only [Finset.sum_apply]
    rw [Finset.sum_insert hi,A.atlasPolynomialVariation_add P ε F (hX i) hs,ih,
      Finset.sum_insert hi]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
