import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialCancellation
import OAI.Geometry.SurfaceImmersion.Correction.AtlasCombinedModes

namespace OAI

/-! Cancel every nonzero quadratic phase of the actual global polynomial
metric using its derived local linearized solvers. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance combinedCancellationFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance combinedCancellationFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance combinedCancellationDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance combinedCancellationDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance combinedCancellationSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance combinedCancellationSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)


theorem global_polynomial_quadratic_cancellation
    {n : A.centers → ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) :
    ∃ (Q : A.centers → Fin 3 → Fin (polynomialFamilyDegree n) → Expression)
      (Dv Dt : ℕ → ℝ) (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ),
      A.PolynomialQuadraticRepresentation P Q ∧
      A.PolynomialLinearRepresentation P Q ∧
      (∀ m, 0 ≤ Dv m) ∧ (∀ m, 0 ≤ Dt m) ∧
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
        (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
        (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
        (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
        (ε τ : ℝ) (s : ℝ≥0)
        (c : ∀ k l, PolynomialSolveData (Q k) ε (A.jetChartMap k F)
          (A.jetChartMap_smooth k hF) (A.globalQuadraticPhase φ k l)
          (A.chartWeightCompact k) τ s),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε →
      (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ 1) → ∀ q : ℕ,
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (Dv m * ∑ k : A.centers, ∑ l,
            (c k l).size (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ k l) q m) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          (Dt m * ∑ k : A.centers, ∑ l,
            (c k l).residual (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ k l) q m)
          (linearMetricTensor F (spaceCoordinates.symm ∘ W)+
            A.atlasPolynomialVariation P ε F (spaceCoordinates.symm ∘ W)+
            (inducedTensor (spaceCoordinates.symm ∘ ∑ a, surfaceMode τ (φ a) (Z a))+
              A.atlasPolynomialQuadratic P ε F
                (spaceCoordinates.symm ∘ ∑ a, surfaceMode τ (φ a) (Z a)))-
            A.globalPolynomialQuadraticMean Q F ε τ φ Z)) := by
  classical
  obtain ⟨Q,Dv,Dt,hQ,hrep,hlin,hDv,hDt,hcancel⟩ :=
    A.atlas_polynomial_finite_cancellation (ι := fun _ => RealModes.QuadraticLabel ι) P hP
  refine ⟨Q,Dv,Dt,hQ,hrep,hlin,hDv,hDt,?_⟩
  intro F hF φ Z hφ hZ ε τ s c hτ hs hτs hs1 hε hsmall q
  obtain ⟨W,hW,hsize,hres⟩ := hcancel F hF (A.globalQuadraticPhase φ)
    (fun i _ => A.chartWeightCompact i) ε τ s c hτ hs hτs hs1 hε hsmall
    (fun _ _ => Subset.rfl) (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ) q
  refine ⟨W,hW,hsize,?_⟩
  have he := A.global_modes_full_quadratic P Q hQ hrep F hF ε τ φ Z hφ hZ
  dsimp only at he
  intro m
  rw [he]
  have ha : linearMetricTensor F (spaceCoordinates.symm ∘ W)+
      A.atlasPolynomialVariation P ε F (spaceCoordinates.symm ∘ W)+
      (A.globalPolynomialQuadraticMean Q F ε τ φ Z+
        A.tensorPlaneRestore (fun i x => ∑ l : RealModes.QuadraticLabel ι,
          QuadraticMean.displacement τ (coordinatePhase (A.globalQuadraticPhase φ i l))
            (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ i l) x))-
      A.globalPolynomialQuadraticMean Q F ε τ φ Z =
      linearMetricTensor F (spaceCoordinates.symm ∘ W)+
        A.atlasPolynomialVariation P ε F (spaceCoordinates.symm ∘ W)+
        A.tensorPlaneRestore (fun i x => ∑ l : RealModes.QuadraticLabel ι,
          QuadraticMean.displacement τ (coordinatePhase (A.globalQuadraticPhase φ i l))
            (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ i l) x) := by abel
  rw [ha]
  exact hres m

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
