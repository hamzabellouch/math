import OAI.Geometry.SurfaceImmersion.Geometry.FixedOrderMetricStep
import OAI.Geometry.SurfaceImmersion.Geometry.ExactInputRecurrence
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasInputBaseline
import OAI.Geometry.SurfaceImmersion.Geometry.NormalizedStepEnvelope
import OAI.Geometry.SurfaceImmersion.Geometry.FixedOrderThreshold
import OAI.Geometry.SurfaceImmersion.Geometry.ExactScaleOrdering

namespace OAI

/-! A genuine correction at the paper's fixed-order scales. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
local instance inputStepFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inputStepFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance inputStepDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance inputStepDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance inputStepSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputStepSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

/-- The actual correction step controls the complete next input in every
order, including orders beyond the finite construction budget. -/
theorem fixed_order_input_step (d : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) (k : ℕ) (hk : 10 ≤ k)
    {B₀ : ℝ} (hB₀ : 0 ≤ B₀) :
    ∃ a ρ ε A₀ : ℝ, 0 < a ∧ 0 < ρ ∧ 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ A₀ ∧
    ∃ B N : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ N m) ∧
    ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
    ∀ t : ℝ, 0 < t → t < ε → ∀ j : ℕ, k ≤ j → j ≤ k+1 →
      d.A.InputBound t (40*(k+1)) B₀ G
        (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
      d.A.WeightedBound 1 2 (ρ/4) (G-F) →
      (∀ x, ‖d.A.tensorEncode (normalizedTensorDefect g.inner (t^(k : ℝ)) G) x -
        d.A.tensorEncode g.inner x‖ ≤ a/8) →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, d.A.WeightedBound (t^(6/5 : ℝ)) m
          (B m*(t^(k : ℝ)*t^(6/5 : ℝ))) U) ∧
        (∀ m ≤ k/2, d.A.WeightedBound 1 m (ρ*t) U) ∧
        ∀ m C, 0 ≤ C → d.A.InputBound t m C G
          (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
          d.A.InputBound (t^(6/5 : ℝ)) m
            (A₀+N m*t^(1/5 : ℝ)*(1+C)) (G+U)
            (normalizedTensorDefect g.inner (t^((6/5 : ℝ)*(j : ℝ))) (G+U)) := by
  classical
  obtain ⟨a,ρ,ε,ha,hρ,hε,hε1,B,L,hB,hL,hstep⟩ := d.fixed_order_metric_step hF k hk hB₀
  obtain ⟨P,hP,hbaseline⟩ := d.A.shifted_zero_bound_of_near hF
  choose Pg hPg hgb using fun m => d.A.exists_bundle_bound
    d.A.tensorTriv d.A.tensorTriv_domain m g.contMDiff
  let N := fun m => Pg m+B (m+2)+L m*(1+B₀)+1+L m
  have hN (m : ℕ) : 0 ≤ N m := by
    dsimp [N]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (hPg m) (hB (m+2)))
      (mul_nonneg (hL m) (by linarith))) zero_le_one) (hL m)
  refine ⟨a,ρ,ε,P+ρ/4+Pg 0,ha,hρ,hε,hε1,add_nonneg (add_nonneg hP (by positivity)) (hPg 0),B,N,hB,hN,?_⟩
  intro G hG t ht htε j hkj hjk hinput hnear hmetric
  obtain ⟨U,hU,hUB,hsmall,herror⟩ := hstep G hG t ht htε j hkj hjk hinput hnear hmetric
  refine ⟨U,hU,hUB,hsmall,?_⟩
  intro m C hC hCm
  have hb := hbaseline G hG (ρ/4) hnear t
  have hUB' : d.A.WeightedBound (t^(6/5 : ℝ)) (2+m)
      (B (m+2)*(t^(k : ℝ)*t^(6/5 : ℝ))) U := by
    simpa only [Nat.add_comm] using hUB (m+2)
  exact d.A.exact_scale_input_recurrence hG hU ht (htε.le.trans hε1) hk
    (by positivity) (hPg 0) (hPg m) (hB (m+2)) hC (hL m) hB₀
    hb hCm.1 hUB' (hgb 0) (hgb m) (herror m C hC hCm)

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
