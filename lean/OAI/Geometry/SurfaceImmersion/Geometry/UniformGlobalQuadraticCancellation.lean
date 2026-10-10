import OAI.Geometry.SurfaceImmersion.Geometry.ScaledGlobalQuadraticCancellation
import OAI.Geometry.SurfaceImmersion.Geometry.QuadraticSolverInputBounds
import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedSolverScale
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasPhaseReadBounds

namespace OAI

/-! Fixed geometric phase solvers give uniform quadratic correction constants. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance uniformQuadraticFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformQuadraticFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance uniformQuadraticDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance uniformQuadraticDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance uniformQuadraticSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformQuadraticSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M) {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem uniform_global_quadratic_cancellation
    {n : A.centers → ℕ}
    (P : (k : A.centers) → Fin 3 → Fin (n k) → JetPolynomial.Expression)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : ι → M → ℝ) (hφ : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (φ i))
    (S : ι → Set M) (hS : ∀ i, IsClosed (S i))
    (c₀ : ∀ k l, PolynomialSolveData (P k) 0 (A.jetChartMap k F)
      (A.jetChartMap_smooth k hF) (A.globalQuadraticPhase φ k l)
      (A.quadraticOverlapCompact S hS k l) 1 1)
    (I : A.centers → RealModes.QuadraticLabel ι → ℕ → ℝ)
    (hI : ∀ k l m, 1 ≤ I k l m)
    (hi : ∀ k l m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c₀ k l).e.target,
      ‖iteratedFDerivWithin ℝ j (c₀ k l).e.symm (c₀ k l).e.target x‖ ≤ I k l m)
    (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (q : ℕ) :
    ∃ Cv Ct : ℕ → ℝ, (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ (τ δ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ δ →
      ∀ (Z : ι → M → Fin 4 → ℂ) (_hZ : ∀ i, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z i)),
      (∀ i, tsupport (Z i) ⊆ S i) →
      (∀ k i m, WeightedEstimates.WeightedBound univ s (m+1) (a m*(δ*τ)) (A.vectorPlaneRead k (Z i))) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2 * Cv m) W) ∧
        (∀ m, A.TensorWeightedBound τ m (δ^2 * (τ/s)^(q+1) * Ct m)
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 •
              RealModes.nonzeroPhaseSum τ (fun i => A.vectorPlaneRead k (φ i))
                (fun i => A.vectorPlaneRead k (Z i)) x))) := by
  classical
  choose R hR hr using fun m => A.phase_read_gradient_bound φ hφ m
  choose B hB hb using fun k m => A.global_quadratic_solver_input_bound (ι := ι) k m (a m) (R m)
  obtain ⟨Dv,Dt,hDv,hDt,hsolve⟩ := A.scaled_global_quadratic_cancellation (ι := ι) P
  let b := fun k l m => tensorChartBudget m (I k l m) (I k l (m+1)) * B k m
  have hbn (k l m) : 0 ≤ b k l m := mul_nonneg
    (tensorChartBudget_nonneg m (zero_le_one.trans (hI k l m)) (zero_le_one.trans (hI k l (m+1)))) (hB k m)
  let cbase := fun k l => (c₀ k l).atUnperturbedScale 1 1 le_rfl
  let Cv := fun m => Dv m * ∑ k : A.centers, ∑ l,
    (cbase k l).sizeFactor q m * b k l (PolynomialSolveData.inputOrder (P := P k) q m)
  let Ct := fun m => Dt m * ∑ k : A.centers, ∑ l,
    (cbase k l).residualFactor q m * b k l (PolynomialSolveData.inputOrder (P := P k) q m)
  refine ⟨Cv,Ct,?_,?_,?_⟩
  · intro m
    exact mul_nonneg (hDv m) (Finset.sum_nonneg (fun k _ => Finset.sum_nonneg
      (fun l _ => mul_nonneg ((cbase k l).sizeFactor_nonneg q m) (hbn k l _))))
  · intro m
    exact mul_nonneg (hDt m) (Finset.sum_nonneg (fun k _ => Finset.sum_nonneg
      (fun l _ => mul_nonneg ((cbase k l).residualFactor_nonneg q m) (hbn k l _))))
  · intro τ δ s hτ hs hτs hs1 hδ Z hZ hSZ hz
    let c := fun k l => (c₀ k l).atUnperturbedScale τ s hs1
    have hn (k l m) : (c k l).norm
        (A.globalQuadraticTargetRestricted τ φ Z hφ hZ S hS hSZ k l) m ≤ δ^2 * b k l m := by
      exact hb k m τ δ s φ Z hφ hZ S hS hSZ hτ hs hτs hs1 hδ (ha m) (hR m)
        (fun i => hz k i m) (fun i v hv => hr m k i s hs.le hs1 v hv)
        l (c k l) (I k l) (hI k l) (hi k l)
    obtain ⟨W,hW,hsize,hres⟩ := hsolve F hF φ Z hφ hZ S hS hSZ c hτ hs hτs hs1 δ q b hn
    exact ⟨W,hW,hsize,hres⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
