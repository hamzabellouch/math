import OAI.Geometry.SurfaceImmersion.Geometry.CardinalityQuadraticCancellation
import OAI.Geometry.SurfaceImmersion.Geometry.ExplicitQuadraticSolverInput
import OAI.Geometry.SurfaceImmersion.Geometry.QuadraticInputBudgets

namespace OAI

/-! Actual global quadratic correction with explicit polynomial budgets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance explicitGlobalQuadraticFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance explicitGlobalQuadraticFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance explicitGlobalQuadraticDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance explicitGlobalQuadraticDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance explicitGlobalQuadraticSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance explicitGlobalQuadraticSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem explicit_global_quadratic_correction :
    ∃ Dv Dt D : ℕ → ℝ, (∀ m, 0 ≤ Dv m) ∧ (∀ m, 0 ≤ Dt m) ∧ (∀ m, 0 ≤ D m) ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι], ∀ n : ℕ, Fintype.card ι ≤ n →
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
        (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
        (_hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
        (_hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
        (S : ι → Set M) (hS : ∀ a, IsClosed (S a)) (_hSZ : ∀ a, tsupport (Z a) ⊆ S a)
        {τ : ℝ} {s : ℝ≥0}
        (c : ∀ k l, PolynomialSolveData emptyMetricPolynomial 0 (A.jetChartMap k F)
          (A.jetChartMap_smooth k hF) (A.globalQuadraticPhase φ k l)
          (A.quadraticOverlapCompact S hS k l) τ s),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → ∀ δ : ℝ, 0 ≤ δ → ∀ q : ℕ,
      ∀ C J I α β : ℕ → ℝ, (∀ m, 1 ≤ I m) → (∀ m, 0 ≤ α m) → (∀ m, 0 ≤ β m) →
      (∀ k l, (c k l).C = C ∧ (c k l).D = (fun _ => 0) ∧ (c k l).J = J) →
      (∀ k l m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c k l).e.target,
        ‖iteratedFDerivWithin ℝ j (c k l).e.symm (c k l).e.target x‖ ≤ I m) →
      (∀ k a m, WeightedEstimates.WeightedBound univ s (m+1) (α m*(δ*τ))
        (A.vectorPlaneRead k (Z a))) →
      (∀ k a m v, ‖v‖ ≤ 1 → WeightedEstimates.WeightedBound univ s m (β m)
        (SmallModes.coordDeriv v (A.vectorPlaneRead k (φ a)))) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (δ^2*(Dv m*(Fintype.card A.centers : ℝ)*((n : ℝ)+2*(n : ℝ)^2)*
            quadraticSizeBudget q m D C J I α β)) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          (δ^2*(τ/s)^(q+1)*(Dt m*(Fintype.card A.centers : ℝ)*((n : ℝ)+2*(n : ℝ)^2)*
            quadraticResidualBudget q m D C J I α β))
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 •
              RealModes.nonzeroPhaseSum τ (fun a => A.vectorPlaneRead k (φ a))
                (fun a => A.vectorPlaneRead k (Z a)) x))) := by
  classical
  choose E hE he using fun (k : A.centers) m =>
    cutoff_square_complex_bound (A.supportedPlaneWeight k) m
  let D := fun m => ∑ k : A.centers, E k m
  have hD (m : ℕ) : 0 ≤ D m := Finset.sum_nonneg (fun k _ => hE k m)
  have hED (k : A.centers) (m : ℕ) : E k m ≤ D m :=
    Finset.single_le_sum (fun i _ => hE i m) (Finset.mem_univ k)
  obtain ⟨Dv,Dt,hDv,hDt,hsolve⟩ := A.cardinality_quadratic_cancellation
  refine ⟨Dv,Dt,D,hDv,hDt,hD,?_⟩
  intro ι inst dec n hn F hF φ Z hφ hZ S hS hSZ τ s c hτ hs hτs hs1 δ hδ q C J I α β hI hα hβ hc hi hz hp
  let N := fun m => quadraticInputBudget m D I α β
  have hN (m : ℕ) : 0 ≤ N m := by
    have ht := tensorChartBudget_nonneg m (zero_le_one.trans (hI m))
      (zero_le_one.trans (hI (m+1)))
    have hd := hD m
    dsimp [N,quadraticInputBudget,quadraticTargetBudget]
    positivity
  have hinput (k : A.centers) (l : RealModes.QuadraticLabel ι) (m : ℕ) :
      (c k l).norm (A.globalQuadraticTargetRestricted τ φ Z hφ hZ S hS hSZ k l) m ≤ δ^2*N m := by
    have hnorm := A.quadratic_solver_input_bound_of_cutoff_bound k m (hE k m) (he k m)
      (α m) (β m) τ δ s φ Z hφ hZ S hS hSZ hτ hs hτs hs1 hδ (hα m) (hβ m)
      (fun a => hz k a m) (fun a v hv => hp k a m v hv) l (c k l) I hI (hi k l)
    have hquad : quadraticTargetBudget m (E k m) (α m) (β m) ≤
        quadraticTargetBudget m (D m) (α m) (β m) := by
      dsimp [quadraticTargetBudget]
      gcongr
      exact hED k m
    have ht := tensorChartBudget_nonneg m (zero_le_one.trans (hI m))
      (zero_le_one.trans (hI (m+1)))
    apply hnorm.trans
    dsimp [N,quadraticInputBudget]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hquad ht) (sq_nonneg δ)
  have hsize (k l m) : (c k l).sizeFactor q m ≤ max 1 (metricForcedSizeBudget C J (fun _ => 1) q m) := by
    rw [(c k l).metric_sizeFactor_eq (fun r => congrFun (hc k l).2.1 r) q m,(hc k l).1,(hc k l).2.2]
    exact le_max_right _ _
  have hres (k l m) : (c k l).residualFactor q m ≤ max 1 (metricForcedResidualBudget C J (fun _ => 1) q m) := by
    rw [(c k l).metric_residualFactor_eq (fun r => congrFun (hc k l).2.1 r) q m,(hc k l).1,(hc k l).2.2]
    exact le_max_right _ _
  obtain ⟨W,hW,hv,ht⟩ := hsolve n hn F hF φ Z hφ hZ S hS hSZ c hτ hs hτs hs1 δ q
    (fun m => max 1 (metricForcedSizeBudget C J (fun _ => 1) q m))
    (fun m => max 1 (metricForcedResidualBudget C J (fun _ => 1) q m)) N
    (fun _ => zero_le_one.trans (le_max_left _ _))
    (fun _ => zero_le_one.trans (le_max_left _ _)) hN hsize hres hinput
  refine ⟨W,hW,?_,?_⟩
  · intro m k
    apply (hv m k).mono_const
    apply le_of_eq
    dsimp [N,quadraticSizeBudget]
    ring
  · intro m k
    apply (ht m k).mono_const
    apply le_of_eq
    dsimp [N,quadraticResidualBudget]
    ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
