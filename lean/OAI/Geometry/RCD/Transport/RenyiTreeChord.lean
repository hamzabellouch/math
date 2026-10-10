import OAI.Geometry.RCD.Transport.RenyiDyadicChord
import OAI.Geometry.RCD.Transport.RenyiPathSemicontinuity

namespace OAI

/-! # All-time scalar Rényi control and endpoint continuity

A fixed maximal midpoint tree has the exact scalar reduced-CD chord at
every time. Weak upper semicontinuity and this lower bound give genuine
continuity of its Rényi entropy at both endpoints.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.plan_following_renyi_tree_chord
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (hK : K ≤ 0)
    {N : ℝ} (hN : (n:ℝ) ≤ N)
    (S : ∀ a : RenyiTransportNode n X, RenyiNodeSplit K (1-1/N) a) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    (hf : ∀ m, FollowsRenyiTree S a (fun t => π.map (fun γ => γ t)) m) :
    (∀ t, reducedChord K (N+1) a.distance (renyiIntegral (hausdorff n X) a.left N)
      (renyiIntegral (hausdorff n X) a.right N) t ≤
        renyiIntegral (hausdorff n X) (π.map (fun γ => γ t)) N) ∧
    ContinuousAt (fun t : Time => renyiIntegral (hausdorff n X) (π.map (fun γ => γ t)) N) 0 ∧
    ContinuousAt (fun t : Time => renyiIntegral (hausdorff n X) (π.map (fun γ => γ t)) N) 1 := by
  let : ProperSpace X := hX.proper K n hn
  let := a.left_probability
  let := a.right_probability
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let B := closedBall a.center (3*a.radius)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ,B] using hX.finiteOnBounded B isBounded_closedBall⟩
  have hs (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), x∈B := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded a.left a.right π hg hp a.center a.radius_nonneg
      a.left_support a.right_support).mono (fun γ hγ => hγ.2 t)
  have he := optimalPlan_endpoints a.left a.right π hp
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hN1 : 1<N := by linarith
  have hNplus : 1<N+1 := by linarith
  have hfin0 : renyiIntegral μ a.left N≠∞ := by
    rw [←he.1]
    exact renyiIntegral_ne_top_of_support μ _ measurableSet_closedBall (hs 0) hN1
  have hfin1 : renyiIntegral μ a.right N≠∞ := by
    rw [←he.2]
    exact renyiIntegral_ne_top_of_support μ _ measurableSet_closedBall (hs 1) hN1
  let v : ProbabilityMeasure C(Time,X) := ⟨π,inferInstance⟩
  have hu := upperSemicontinuous_supported_renyiPath μ measurableSet_closedBall
    (fun t => v.map (fun γ => γ t)) (continuous_time_marginals v) hs hN1
  have hc := continuous_reducedChord hK hNplus a.distance_nonneg hfin0 hfin1
  have hall : ∀ t, reducedChord K (N+1) a.distance (renyiIntegral μ a.left N)
      (renyiIntegral μ a.right N) t ≤ renyiIntegral μ (π.map (fun γ => γ t)) N := by
    apply ge_continuous_of_dense hu hc dense_dyadicGrid
    intro t ht
    obtain ⟨m,hm⟩ := mem_iUnion.mp ht
    exact (hf m).reducedChord K n hn hX hK hN S m t hm
  refine ⟨hall,continuousAt_of_upperSemicontinuous_lower hu hc hall 0 ?_,
    continuousAt_of_upperSemicontinuous_lower hu hc hall 1 ?_⟩
  · rw [reducedChord_zero hK hNplus a.distance_nonneg]
    change renyiIntegral μ a.left N=renyiIntegral μ (π.map (fun γ => γ 0)) N
    rw [he.1]
  · rw [reducedChord_one hK hNplus a.distance_nonneg]
    change renyiIntegral μ a.right N=renyiIntegral μ (π.map (fun γ => γ 1)) N
    rw [he.2]

end RegularPointCoordinates

end

end OAI
