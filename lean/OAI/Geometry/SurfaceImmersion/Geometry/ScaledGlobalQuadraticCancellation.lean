import OAI.Geometry.SurfaceImmersion.Geometry.OverlapQuadraticCancellation
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSolveFactors

namespace OAI

/-! Explicit amplitude and residual powers in the global quadratic cancellation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance scaledGlobalFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance scaledGlobalFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance scaledGlobalDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance scaledGlobalDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance scaledGlobalSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance scaledGlobalSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scaled_global_quadratic_cancellation
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
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → ∀ (δ : ℝ) (q : ℕ)
        (b : A.centers → RealModes.QuadraticLabel ι → ℕ → ℝ),
      (∀ k l m, (c k l).norm (A.globalQuadraticTargetRestricted τ φ Z hφ hZ S hS hSZ k l) m
        ≤ δ^2 * b k l m) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (δ^2 * (Dv m * ∑ k : A.centers, ∑ l,
            (c k l).sizeFactor q m * b k l (PolynomialSolveData.inputOrder (P := P k) q m))) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          (δ^2 * (τ/s)^(q+1) * (Dt m * ∑ k : A.centers, ∑ l,
            (c k l).residualFactor q m * b k l (PolynomialSolveData.inputOrder (P := P k) q m)))
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 •
              RealModes.nonzeroPhaseSum τ (fun a => A.vectorPlaneRead k (φ a))
                (fun a => A.vectorPlaneRead k (Z a)) x))) := by
  obtain ⟨Dv,Dt,hDv,hDt,h⟩ := A.global_quadratic_cancellation_on (ι := ι) P
  refine ⟨Dv,Dt,hDv,hDt,?_⟩
  intro F hF φ Z hφ hZ S hS hSZ τ s c hτ hs hτs hs1 δ q b hb
  obtain ⟨W,hW,hsize,hres⟩ := h F hF φ Z hφ hZ S hS hSZ c hτ hs hτs hs1 q
  refine ⟨W,hW,?_,?_⟩
  · intro m k
    apply (hsize m k).mono_const
    rw [mul_left_comm (δ^2)]
    apply mul_le_mul_of_nonneg_left _ (hDv m)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    exact (c i l).size_le_scaled (sq_nonneg δ) _ q m (hb i l _)
  · intro m k
    apply (hres m k).mono_const
    have he : δ^2 * (τ/s)^(q+1) * (Dt m * ∑ i : A.centers, ∑ l,
        (c i l).residualFactor q m * b i l (PolynomialSolveData.inputOrder (P := P i) q m)) =
        Dt m * ∑ i : A.centers, ∑ l, δ^2 * (τ/s)^(q+1) *
          ((c i l).residualFactor q m * b i l (PolynomialSolveData.inputOrder (P := P i) q m)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (hDt m)
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro l _
    have hh := (c i l).residual_le_scaled
      (by simpa only [zero_div,add_zero] using div_nonneg hτ.le hs.le) _ q m (hb i l _)
    simpa only [zero_div,add_zero] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
