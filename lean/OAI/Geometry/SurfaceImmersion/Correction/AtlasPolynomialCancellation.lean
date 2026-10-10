import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialLinearized
import OAI.Geometry.SurfaceImmersion.Correction.FinitePolynomialCancellation

namespace OAI

/-! Finite cancellation for the derivative of the actual globally restored
polynomial metric, with local polynomials derived from that metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance polyCancellationFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polyCancellationFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polyCancellationDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polyCancellationDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polyCancellationSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polyCancellationSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_polynomial_finite_cancellation
    {n : A.centers → ℕ} {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) :
    ∃ (Q : A.centers → Fin 3 → Fin (polynomialFamilyDegree n) → Expression)
      (Dv Dt : ℕ → ℝ),
      (∀ i k l, (Q i k l).SmoothCoeffs univ) ∧
      A.PolynomialQuadraticRepresentation P Q ∧
      A.PolynomialLinearRepresentation P Q ∧
      (∀ m, 0 ≤ Dv m) ∧ (∀ m, 0 ≤ Dt m) ∧
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
        (φ : ∀ i : A.centers, ι i → Base → ℝ)
        (K : ∀ i : A.centers, ι i → TopologicalSpace.Compacts Base)
        (ε τ : ℝ) (s : ℝ≥0)
        (c : ∀ i j, PolynomialSolveData (Q i) ε (A.jetChartMap i F)
          (A.jetChartMap_smooth i hF) (φ i j) (K i j) τ s),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε →
      (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ 1) →
      (∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ target : ∀ i j, SupportedField (F := ComplexTensor) (modeSupport (K i j)), ∀ q : ℕ,
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (Dv m * ∑ i : A.centers, ∑ j, (c i j).size (target i j) q m) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          (Dt m * ∑ i : A.centers, ∑ j, (c i j).residual (target i j) q m)
          (linearMetricTensor F (spaceCoordinates.symm ∘ W)+
            A.atlasPolynomialVariation P ε F (spaceCoordinates.symm ∘ W)+
            A.tensorPlaneRestore (fun i x => ∑ j,
              QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x))) := by
  classical
  obtain ⟨Q,hQ,hquad,hrepr⟩ := A.full_linearized_representatives P hP
  choose Dv hDv hv using fun m => A.vectorPlaneRestore_bound (V := RealModes.RVec 4) m
  choose Dt hDt ht using fun m => A.tensorPlaneRestore_bound m
  refine ⟨Q,Dv,Dt,hQ,hquad,hrepr,hDv,hDt,?_⟩
  intro F hF φ K ε τ s c hτ hs hτs hs1 hε hsmall hK target q
  choose X hX hsupport hsize hres using fun i : A.centers =>
    finite_polynomial_cancellation (Q i) ε (A.jetChartMap_smooth i hF) (φ i) (K i) (c i)
      hτ hs hτs hs1 hε (hsmall i) (target i) q
  have hsp (i : A.centers) : tsupport (X i) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hsupport i hx)
    exact hK i j hj
  let T : A.centers → SmallModes.Base → Tensor := fun i x => ∑ j,
    QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x
  have hT (i : A.centers) : ContDiff ℝ ∞ (T i) := by
    apply ContDiff.sum
    intro j _
    exact contDiffOn_univ.mp (RealModes.contDiffOn_displacement
      ((c i j).smoothPhase.comp planeCoordinateIsometry.symm.contDiff).contDiffOn
      (target i j).contDiff.contDiffOn τ)
  have hsz (i : A.centers) (m : ℕ) : 0 ≤ ∑ j, (c i j).size (target i j) q m :=
    Finset.sum_nonneg (fun j _ => (c i j).size_nonneg (target i j) q m)
  have hrr (i : A.centers) (m : ℕ) : 0 ≤ ∑ j, (c i j).residual (target i j) q m :=
    Finset.sum_nonneg (fun j _ => (c i j).residual_nonneg
      (add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _)))
      (target i j) q m)
  refine ⟨A.vectorPlaneRestore X,A.vectorPlaneRestore_smooth X hX,?_,?_⟩
  · intro m
    apply hv m X τ (∑ i : A.centers, ∑ j, (c i j).size (target i j) q m)
      hτ (hτs.trans hs1) (Finset.sum_nonneg (fun i _ => hsz i m)) hX
    intro i
    exact (hsize i m).mono_const (Finset.single_le_sum (fun k _ => hsz k m) (Finset.mem_univ i))
  · intro m
    rw [hrepr F hF X hX hsp ε,← A.tensorPlaneRestore_add]
    apply ht m _ τ (∑ i : A.centers, ∑ j, (c i j).residual (target i j) q m)
      hτ (hτs.trans hs1) (Finset.sum_nonneg (fun i _ => hrr i m))
    · intro i
      apply ContDiff.add _ (hT i)
      exact coordinateFullLinearized_smooth isOpen_univ isOpen_univ (Q i) (hQ i)
        (A.jetChartMap_smooth i hF) (fun _ _ => mem_univ _)
        (A.chartWeightCompact i) (subset_univ _) (hX i) (hsp i) ε
    · intro i
      exact (hres i m).mono_const (Finset.single_le_sum (fun k _ => hrr k m) (Finset.mem_univ i))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
