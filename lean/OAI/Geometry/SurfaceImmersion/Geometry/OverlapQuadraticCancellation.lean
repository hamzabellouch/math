import OAI.Geometry.SurfaceImmersion.Geometry.QuadraticOverlapSupports

namespace OAI

/-! Finite cancellation using actual compact support intersections. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance overlapCancellationFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance overlapCancellationFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance overlapCancellationDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance overlapCancellationDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance overlapCancellationSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance overlapCancellationSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem global_quadratic_cancellation_on
    {n : A.centers → ℕ}
    (P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression) :
    ∃ Dv Dt : ℕ → ℝ, (∀ m, 0 ≤ Dv m) ∧ (∀ m, 0 ≤ Dt m) ∧
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
        (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
        (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
        (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
        (S : ι → Set M) (hS : ∀ a, IsClosed (S a)) (hSZ : ∀ a, tsupport (Z a) ⊆ S a)
        {τ : ℝ} {s : ℝ≥0}
        (c : ∀ k l, PolynomialSolveData (P k) 0 (A.jetChartMap k F)
          (A.jetChartMap_smooth k hF) (A.globalQuadraticPhase φ k l)
          (A.quadraticOverlapCompact S hS k l) τ s),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → ∀ q : ℕ,
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (Dv m * ∑ k : A.centers, ∑ l, (c k l).size (A.globalQuadraticTargetRestricted τ φ Z hφ hZ S hS hSZ k l) q m) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          (Dt m * ∑ k : A.centers, ∑ l, (c k l).residual (A.globalQuadraticTargetRestricted τ φ Z hφ hZ S hS hSZ k l) q m)
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 •
              RealModes.nonzeroPhaseSum τ (fun a => A.vectorPlaneRead k (φ a))
                (fun a => A.vectorPlaneRead k (Z a)) x))) := by
  classical
  obtain ⟨Dv,Dt,hDv,hDt,h⟩ := A.atlas_finite_cancellation
    (ι := fun _ => RealModes.QuadraticLabel ι) P
  refine ⟨Dv,Dt,hDv,hDt,?_⟩
  intro F hF φ Z hφ hZ S hS hSZ τ s c hτ hs hτs hs1 q
  obtain ⟨W,hW,hsize,hres⟩ := h F hF (A.globalQuadraticPhase φ)
    (A.quadraticOverlapCompact S hS) c hτ hs hτs hs1
    (fun k l => Set.image_mono (A.quadraticOverlapCompact_subset S hS k l))
    (A.globalQuadraticTargetRestricted τ φ Z hφ hZ S hS hSZ) q
  refine ⟨W,hW,hsize,?_⟩
  intro m
  rw [A.globalQuadraticTarget_expansion τ φ Z hφ hZ]
  exact hres m

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
