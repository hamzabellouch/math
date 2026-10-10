import OAI.Geometry.RCD.Transport.RenyiTreeCompactness

namespace OAI

/-! # Uniform compression on the fixed maximal midpoint tree

Dyadic marginals are fixed before compactness. Their common density bound
extends to every time by weak continuity and closedness of domination.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem isClosed_probability_domination [ProperSpace X] [SeparableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {C : ℝ≥0∞} (hC : C ≠ ∞) :
    IsClosed {ν : ProbabilityMeasure X | (ν : Measure X) ≤ C • μ} := by
  convert (lowerSemicontinuous_transportExcessMass μ hC).isClosed_preimage 0 using 1
  ext ν
  simp only [mem_ofPred_eq, mem_preimage, mem_Iic, nonpos_iff_eq_zero,
    transportExcessMass_zero_iff μ (ν : Measure X) hC]

theorem NoncollapsedRCD.plan_following_renyi_tree_compression
    [SeparableSpace X] [CompleteSpace X]
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) {q : ℝ}
    (S : ∀ a : RenyiTransportNode n X, RenyiNodeSplit K q a) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    (hf : ∀ m, FollowsRenyiTree S a (fun t => π.map (fun γ => γ t)) m) :
    ∀ t : Time, π.map (fun γ => γ t) ≤ compressionBudget K n a.distance a.capacity • hausdorff n X := by
  let : ProperSpace X := hX.proper K n hn
  let := a.left_probability
  let := a.right_probability
  let μ := hausdorff n X
  let B := closedBall a.center (3*a.radius)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ,B] using hX.finiteOnBounded B isBounded_closedBall⟩
  let v : ProbabilityMeasure C(Time,X) := ⟨π,inferInstance⟩
  let cap := compressionBudget K n a.distance a.capacity
  have hc : cap ≠ ∞ := compressionBudget_ne_top K n a.distance a.capacity_finite
  have hs (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), x∈B := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded a.left a.right π hg hp a.center a.radius_nonneg
      a.left_support a.right_support).mono (fun γ hγ => hγ.2 t)
  let T : Set Time := {t | π.map (fun γ => γ t) ≤ cap • μ.restrict B}
  have hT : IsClosed T := (isClosed_probability_domination (μ.restrict B) hc).preimage
    (continuous_time_marginals v)
  have hd : (⋃ m, dyadicGrid m) ⊆ T := by
    intro t ht
    exact (compression_iff_localized μ _ (hs t) cap).mp
      (plan_following_renyi_tree_dyadic_compression S a π hf ht)
  have hall := closure_minimal hd hT
  rw [dense_dyadicGrid.closure_eq] at hall
  intro t
  exact (compression_iff_localized μ _ (hs t) cap).mpr (hall (mem_univ t))

end RegularPointCoordinates

end

end OAI
