import OAI.Geometry.SurfaceImmersion.Correction.UniformRadiusSmoothedMetricIncrement
import OAI.Geometry.SurfaceImmersion.Correction.ActualSmoothedStep
import OAI.Geometry.SurfaceImmersion.Correction.UniformSmoothingInputProfiles
import OAI.Geometry.SurfaceImmersion.Geometry.CompactSectionBounds
import OAI.Geometry.SurfaceImmersion.Correction.GlobalSmoothedMetricStep
import OAI.Geometry.SurfaceImmersion.Correction.TensorSmoothingSymmetry
import OAI.Geometry.SurfaceImmersion.Correction.SmoothedInputAdmissibility
import OAI.Geometry.SurfaceImmersion.Geometry.GlobalInputRecurrence

namespace OAI

/-! Actual smoothed correction with one geometric neighborhood for all orders. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
local instance uniformRadiusActualFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformRadiusActualFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance uniformRadiusActualDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance uniformRadiusActualDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance uniformRadiusActualSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformRadiusActualSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

/-- The map and tensor radii and the metric norm bound are chosen once;
only analytic profiles and scale thresholds vary with the orders. -/
theorem uniform_radius_actual_step (d : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ∃ a ρ K : ℝ, 0 < a ∧ 0 < ρ ∧ 0 ≤ K ∧
    ∀ r : ℕ, ∃ D : ℝ, 0 ≤ D ∧
    ∀ (q : ℕ) (B₀ : ℝ), 0 ≤ B₀ →
    ∃ (η : ℝ) (B T Dm Em : ℕ → ℝ), 0 < η ∧ η ≤ 1 ∧
      (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧ (∀ m, 0 ≤ Dm m) ∧ (∀ m, 0 ≤ Em m) ∧
    ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
    ∀ δ δ' t s τ : ℝ, 0 < δ → 0 < δ' → δ' ≤ δ →
      0 < t → t ≤ 1 → 0 < s → s ≤ t → 0 < τ → τ ≤ s → τ/s ≤ η → δ ≤ τ →
      d.A.InputBound t r B₀ G (normalizedTensorDefect g.inner δ G) →
      d.A.WeightedBound 1 2 (ρ/4) (G-F) →
      (∀ x, ‖d.A.tensorEncode (normalizedTensorDefect g.inner δ G) x -
        d.A.tensorEncode g.inner x‖ ≤ a/8) →
      D*B₀*(s/t)^r ≤ min (ρ/4) (a/8) → (δ'/δ)^2*K ≤ a/8 →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, d.A.WeightedBound τ m (B m*(δ*τ)) U) ∧
        ∀ m C, 0 ≤ C → d.A.InputBound t m C G (normalizedTensorDefect g.inner δ G) →
          d.A.TensorWeightedBound τ m
            (normalizedStepBound r q B₀ (Dm m) (Em m) (B (m+1)) (T m) C δ δ' τ s t)
            (normalizedTensorDefect g.inner δ' (G+U)-g.inner) := by
  classical
  obtain ⟨a,ρ,K,ha,hρ,hK,hall⟩ := d.uniform_radius_smoothed_increment_of_input hF
  refine ⟨a,ρ,K,ha,hρ,hK,?_⟩
  intro r
  obtain ⟨D,hD,hr⟩ := hall r
  refine ⟨D,hD,?_⟩
  intro q B₀ hB₀
  obtain ⟨η,B,T,hη,hη1,hB,hT,hbuild⟩ := hr q B₀ hB₀
  choose Dm Em hDm hEm hmetric using fun m => d.A.smoothed_normalized_metric_step_bound r m
  refine ⟨η,B,T,Dm,Em,hη,hη1,hB,hT,hDm,hEm,?_⟩
  intro G hG δ δ' t s τ hδ hδ' hδ'δ ht ht1 hs hst hτ hτs hτη hδτ
    hinput hnear hHnear htail hratio
  let H := normalizedTensorDefect g.inner δ G
  have hH := d.A.normalizedTensorDefect_smooth g.contMDiff δ hG
  have hsym : ∀ p v w, H p v w = H p w v := by
    intro p v w
    change (δ^2)⁻¹ * (g.inner p v w - inducedTensor G p v w) =
      (δ^2)⁻¹ * (g.inner p w v - inducedTensor G p w v)
    rw [g.symm p v w,inducedTensor_symmetric G p v w]
  obtain ⟨U,hU,hUB,hUE⟩ := hbuild G H hG hH hsym t s ht ht1 hs hst hinput
    hnear hHnear htail δ δ' τ hδ hδ'.le hδ'δ hτ hτs hτη hδτ hratio
  refine ⟨U,hU,hUB,?_⟩
  intro m C hC hCm
  exact hmetric m g.inner g.contMDiff G U hG hU δ δ' τ s t B₀ C
    (B (m+1)*(δ*τ)) (T m*(δ*(τ/s)^(q+1)+δ^3/τ))
    hδ.ne' hδ'.ne' hτ hτs hst ht1 hB₀ hC
    (mul_nonneg (hB _) (mul_nonneg hδ.le hτ.le)) hinput hCm (hUB (m+1)) (hUE m)

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
