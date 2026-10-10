import OAI.Geometry.SurfaceImmersion.Geometry.CompactGeometrySmallIncrement
import OAI.Geometry.SurfaceImmersion.Atlas.MetricGoodPhaseData

namespace OAI

/-! An actual metric-adapted immersion supplies all the small-increment geometry. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
local instance metricSmallFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricSmallFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance metricSmallDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricSmallDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricSmallSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricSmallSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

/-- All geometric and mean-solver inputs are constructed from the metric and
immersion. Only the nearby map's explicit analytic bounds remain. -/
theorem small_increment (d : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m)
    (hPF : ∀ m, d.A.ShiftedBound 2 m 1 (P m) F) (q : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) →
      ∃ (ρ₀ η₀ : ℝ) (B T : ℕ → ℝ), 0 < ρ₀ ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧
        (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → d.A.WeightedBound 1 2 b (G-F) →
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, d.A.ShiftedBound 2 m s (P m) G) →
      ∀ (H : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x v v', H x v v' = H x v' v) →
      (∀ x, ‖d.A.tensorEncode H x - d.A.tensorEncode g.inner x‖ ≤ r/2) →
      (∀ m, d.A.TensorWeightedBound s m (C m) H) →
      ∀ τ δ : ℝ, 0 < τ → τ ≤ s → τ/s ≤ η₀ → 0 < δ → δ ≤ τ →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, d.A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, d.A.TensorWeightedBound τ m (T m*(δ*(τ/s)^(q+1)+δ^3/τ))
          (inducedTensor (G+X) - inducedTensor G - δ^2 • H)) := by
  exact d.A.compact_geometry_small_increment F hF d.Q d.w
    (fun i j => (d.weight_pos i j).ne') d.immersion d.pure_good g.inner
    g.contMDiff d.metric_positive d.quadratic_good P hP hPF q

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
