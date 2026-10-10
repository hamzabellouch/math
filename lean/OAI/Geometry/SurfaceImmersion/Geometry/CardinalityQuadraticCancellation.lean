import OAI.Geometry.SurfaceImmersion.Geometry.UniformQuadraticLabelCancellation
import OAI.Geometry.SurfaceImmersion.Geometry.MetricForcedFactorBudgets

namespace OAI

/-! Global quadratic cancellation with explicit polynomial dependence on
the number of free phases. Atlas constants precede all finite label types. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance cardinalityQuadraticFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance cardinalityQuadraticFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance cardinalityQuadraticDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance cardinalityQuadraticDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance cardinalityQuadraticSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cardinalityQuadraticSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma quadratic_family_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : Fintype.card ι ≤ n) {B : ℝ} (hB : 0 ≤ B)
    (f : A.centers → RealModes.QuadraticLabel ι → ℝ) (hf : ∀ k l, f k l ≤ B) :
    (∑ k : A.centers, ∑ l, f k l) ≤
      (Fintype.card A.centers : ℝ)*((n : ℝ)+2*(n : ℝ)^2)*B := by
  have hc : Fintype.card (RealModes.QuadraticLabel ι) ≤ n+2*n^2 := by
    apply (RealModes.card_quadraticLabel_le ι).trans
    gcongr
  have hcr : (Fintype.card (RealModes.QuadraticLabel ι) : ℝ) ≤ (n : ℝ)+2*(n : ℝ)^2 := by
    exact_mod_cast hc
  calc
    (∑ k : A.centers, ∑ l, f k l) ≤ ∑ _k : A.centers, ∑ _l : RealModes.QuadraticLabel ι, B :=
      Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => hf k l))
    _ = (Fintype.card A.centers : ℝ)*(Fintype.card (RealModes.QuadraticLabel ι) : ℝ)*B := by simp; ring
    _ ≤ _ := by gcongr

theorem cardinality_quadratic_cancellation :
    ∃ Dv Dt : ℕ → ℝ, (∀ m, 0 ≤ Dv m) ∧ (∀ m, 0 ≤ Dt m) ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι], ∀ n : ℕ, Fintype.card ι ≤ n →
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
        (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
        (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
        (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
        (S : ι → Set M) (hS : ∀ a, IsClosed (S a)) (hSZ : ∀ a, tsupport (Z a) ⊆ S a)
        {τ : ℝ} {s : ℝ≥0}
        (c : ∀ k l, PolynomialSolveData emptyMetricPolynomial 0 (A.jetChartMap k F)
          (A.jetChartMap_smooth k hF) (A.globalQuadraticPhase φ k l)
          (A.quadraticOverlapCompact S hS k l) τ s),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → ∀ δ : ℝ, ∀ q : ℕ,
      ∀ Sv St N : ℕ → ℝ, (∀ m, 0 ≤ Sv m) → (∀ m, 0 ≤ St m) → (∀ m, 0 ≤ N m) →
      (∀ k l m, (c k l).sizeFactor q m ≤ Sv m) →
      (∀ k l m, (c k l).residualFactor q m ≤ St m) →
      (∀ k l m, (c k l).norm (A.globalQuadraticTargetRestricted τ φ Z hφ hZ S hS hSZ k l) m
        ≤ δ^2*N m) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (δ^2*(Dv m*(Fintype.card A.centers : ℝ)*((n : ℝ)+2*(n : ℝ)^2)*Sv m*N (m+q+1))) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          (δ^2*(τ/s)^(q+1)*(Dt m*(Fintype.card A.centers : ℝ)*((n : ℝ)+2*(n : ℝ)^2)*St m*N (m+q+1)))
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 •
              RealModes.nonzeroPhaseSum τ (fun a => A.vectorPlaneRead k (φ a))
                (fun a => A.vectorPlaneRead k (Z a)) x))) := by
  classical
  obtain ⟨Dv,Dt,hDv,hDt,h⟩ := A.uniform_global_quadratic_cancellation_on (fun _ => emptyMetricPolynomial)
  refine ⟨Dv,Dt,hDv,hDt,?_⟩
  intro ι inst dec n hn F hF φ Z hφ hZ S hS hSZ τ s c hτ hs hτs hs1 δ q Sv St N hSv hSt hN hcv hct hcn
  obtain ⟨W,hW,hsize,hres⟩ := h F hF φ Z hφ hZ S hS hSZ c hτ hs hτs hs1 q
  have horder (m : ℕ) : PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m = m+q+1 := by
    simp only [PolynomialSolveData.inputOrder,tensorOrder_emptyMetricPolynomial]
    omega
  have hsz (m : ℕ) := A.quadratic_family_sum_le hn
    (mul_nonneg (sq_nonneg δ) (mul_nonneg (hSv m) (hN (m+q+1))))
    (fun k l => (c k l).size (A.globalQuadraticTargetRestricted τ φ Z hφ hZ S hS hSZ k l) q m)
    (fun k l => ((c k l).size_le_scaled (sq_nonneg δ) _ q m (hcn k l _)).trans (by
      rw [horder]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hcv k l m) (hN _)) (sq_nonneg δ)))
  have hr (m : ℕ) := A.quadratic_family_sum_le hn
    (mul_nonneg (mul_nonneg (sq_nonneg δ) (pow_nonneg (div_nonneg hτ.le hs.le) _))
      (mul_nonneg (hSt m) (hN (m+q+1))))
    (fun k l => (c k l).residual (A.globalQuadraticTargetRestricted τ φ Z hφ hZ S hS hSZ k l) q m)
    (fun k l => ((c k l).residual_le_scaled
      (by simpa only [zero_div,add_zero] using div_nonneg hτ.le hs.le) _ q m (hcn k l _)).trans (by
      simp only [zero_div,add_zero,horder]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hct k l m) (hN _))
        (mul_nonneg (sq_nonneg δ) (pow_nonneg (div_nonneg hτ.le hs.le) _))))
  refine ⟨W,hW,?_,?_⟩
  · intro m k
    apply (hsize m k).mono_const
    apply (mul_le_mul_of_nonneg_left (hsz m) (hDv m)).trans
    apply le_of_eq
    ring
  · intro m k
    apply (hres m k).mono_const
    apply (mul_le_mul_of_nonneg_left (hr m) (hDt m)).trans
    apply le_of_eq
    ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
