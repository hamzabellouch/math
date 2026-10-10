import OAI.Geometry.SurfaceImmersion.Correction.AtlasRestoredPolynomialDirection
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialLinearity

namespace OAI

/-! The actual global polynomial linearization is assembled from the
constructed local representatives, for every supported family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance polynomialAssemblyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialAssemblyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialAssemblyDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialAssemblyDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialAssemblySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialAssemblySectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem polynomial_linearized_representatives {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) :
    ∃ Q : A.centers → Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ i k r, (Q i k r).SmoothCoeffs univ) ∧
      A.PolynomialQuadraticRepresentation P Q ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ∀ (X : A.centers → RealModes.RField 4), (∀ i, ContDiff ℝ ∞ (X i)) →
      (∀ i, tsupport (X i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ ε : ℝ,
        A.atlasPolynomialVariation P ε F (spaceCoordinates.symm ∘ A.vectorPlaneRestore X) =
          A.tensorPlaneRestore (fun i => coordinateRealLinearized (Q i) ε (A.jetChartMap i F) (X i) 0) := by
  classical
  choose Q hQ _ hfirst hsecond using fun i => A.atlas_polynomial_local_model P hP i
  refine ⟨Q,hQ,?_,?_⟩
  · intro F X hF hX i x hx ε
    exact hsecond i F X hF hX x hx ε
  · intro F hF X hX hsp ε
    let Y : A.centers → M → Space := fun i => restore (i : M) (A.outer i)
      ((spaceCoordinates.symm ∘ X i) ∘ planeCoordinateIsometry)
    have hY (i : A.centers) : ContMDiff planeModel spaceModel ∞ (Y i) :=
      restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
        ((spaceCoordinates.symm.contDiff.comp (hX i)).comp planeCoordinateIsometry.contDiff)
    have hdir (i : A.centers) : A.atlasPolynomialVariation P ε F (Y i) =
        A.bundleRestore A.tensorTriv i (fun x => fiberFromThree
          (coordinateRealLinearized (Q i) ε (A.jetChartMap i F) (X i) 0 (planeCoordinateIsometry x))) := by
      apply A.restored_polynomial_direction P i (Q i) F (X i) (hsp i) ε
      intro x hx
      have hh := hfirst i F (Y i) hF (hY i) x hx ε
      have he : A.jetChartMap i (Y i) ∘ planeCoordinateIsometry.symm = X i := by
        rw [show Y i = restore (i : M) (A.outer i)
          ((spaceCoordinates.symm ∘ X i) ∘ planeCoordinateIsometry) from rfl,
          A.jetChartMap_restored_direction i (X i) (hsp i)]
        funext y
        simp only [Function.comp_apply,planeCoordinateIsometry.apply_symm_apply]
      rwa [he] at hh
    have he : spaceCoordinates.symm ∘ A.vectorPlaneRestore X = ∑ i : A.centers, Y i :=
      A.euclidean_vectorPlaneRestore X
    rw [he,A.atlasPolynomialVariation_sum P ε F Finset.univ Y hY]
    funext p
    simp only [tensorPlaneRestore,Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (hdir i) p

/-- The local linearized operators act on the same global polynomial metric. -/
def PolynomialLinearRepresentation {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression) : Prop :=
  ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ∀ (X : A.centers → RealModes.RField 4), (∀ i, ContDiff ℝ ∞ (X i)) →
      (∀ i, tsupport (X i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ ε : ℝ,
        linearMetricTensor F (spaceCoordinates.symm ∘ A.vectorPlaneRestore X)+
            A.atlasPolynomialVariation P ε F (spaceCoordinates.symm ∘ A.vectorPlaneRestore X) =
          A.tensorPlaneRestore (fun i => coordinateFullLinearized (Q i) ε (A.jetChartMap i F) (X i))

theorem full_linearized_representatives {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) :
    ∃ Q : A.centers → Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ i k r, (Q i k r).SmoothCoeffs univ) ∧
      A.PolynomialQuadraticRepresentation P Q ∧
      A.PolynomialLinearRepresentation P Q := by
  obtain ⟨Q,hQ,hquad,hpoly⟩ := A.polynomial_linearized_representatives P hP
  refine ⟨Q,hQ,hquad,?_⟩
  intro F hF X hX hsp ε
  rw [A.euclidean_vectorPlaneRestore_linearized hF X hX hsp,hpoly F hF X hX hsp ε,
    ← A.tensorPlaneRestore_add]
  congr 1

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
