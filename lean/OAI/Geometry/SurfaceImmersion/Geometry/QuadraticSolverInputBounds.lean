import OAI.Geometry.SurfaceImmersion.Atlas.AtlasQuadraticBounds
import OAI.Geometry.SurfaceImmersion.Geometry.QuadraticOverlapSupports
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialInputNorm

namespace OAI

/-! Actual supported quadratic targets in the norm used by each phase solver. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance solverInputFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance solverInputFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance solverInputDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance solverInputDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance solverInputSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance solverInputSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M) {ι : Type*}

theorem global_quadratic_solver_input_bound (k : A.centers) (m : ℕ) (A₀ P₀ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ δ : ℝ) (s : ℝ≥0)
      (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
      (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
      (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
      (S : ι → Set M) (hS : ∀ a, IsClosed (S a)) (hSZ : ∀ a, tsupport (Z a) ⊆ S a),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ δ → 0 ≤ A₀ → 0 ≤ P₀ →
      (∀ a, WeightedEstimates.WeightedBound univ s (m+1) (A₀*(δ*τ)) (A.vectorPlaneRead k (Z a))) →
      (∀ a v, ‖v‖ ≤ 1 → WeightedEstimates.WeightedBound univ s m P₀
        (SmallModes.coordDeriv v (A.vectorPlaneRead k (φ a)))) →
      ∀ (l : RealModes.QuadraticLabel ι) {n : ℕ} {P : Fin 3 → Fin n → JetPolynomial.Expression}
        {G : JetPolynomial.Base → JetPolynomial.Space} {hG : ContDiff ℝ ∞ G}
        (c : PolynomialSolveData P 0 G hG (A.globalQuadraticPhase φ k l)
          (A.quadraticOverlapCompact S hS k l) τ s)
        (I : ℕ → ℝ), (∀ j, 1 ≤ I j) →
      (∀ a j, 1 ≤ j → j ≤ a → ∀ x ∈ c.e.target,
        ‖iteratedFDerivWithin ℝ j c.e.symm c.e.target x‖ ≤ I a) →
      c.norm (A.globalQuadraticTargetRestricted τ φ Z hφ hZ S hS hSZ k l) m ≤
        δ^2 * (tensorChartBudget m (I m) (I (m+1)) * B) := by
  obtain ⟨B,hB,hb⟩ := A.globalQuadraticTarget_bound (ι := ι) k m A₀ P₀
  refine ⟨B,hB,?_⟩
  intro τ δ s φ Z hφ hZ S hS hSZ hτ hs hτs hs1 hδ hA hP hz hp l n P G hG c I hI hi
  have ht : WeightedEstimates.WeightedBound univ s m (B*δ^2)
      (A.globalQuadraticTargetRestricted τ φ Z hφ hZ S hS hSZ k l) :=
    hb τ s δ φ Z hφ hZ hτ hs hτs hs1 hδ hA hP hz hp l
  have hh := c.norm_le_of_weightedBound hs hs1 I hI hi m
    (mul_nonneg hB (sq_nonneg δ)) _ ht
  calc
    _ ≤ tensorChartBudget m (I m) (I (m+1)) * (B*δ^2) := hh
    _ = _ := by ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
