import OAI.Geometry.RCD.Transport.RenyiTreeClosed

namespace OAI

/-! # A single optimal plan realizes every level of the fixed midpoint tree -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem exists_plan_following_all_renyi_levels {n : ℕ} {K q : ℝ}
    (S : ∀ a : RenyiTransportNode n X, RenyiNodeSplit K q a) (a : RenyiTransportNode n X) :
    ∃ π : Measure C(Time,X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧ IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))) ∧
      ∀ m, FollowsRenyiTree S a (fun t => π.map (fun γ => γ t)) m := by
  let v₀ : ProbabilityMeasure X := ⟨a.left,a.left_probability⟩
  let v₁ : ProbabilityMeasure X := ⟨a.right,a.right_probability⟩
  let A := OptimalGeodesicPlans v₀ v₁
  let Q : ℕ → Set (ProbabilityMeasure C(Time,X)) := fun m =>
    {π | FollowsRenyiTree S a (fun t => (π:Measure C(Time,X)).map (fun γ => γ t)) m}
  have hA : IsCompact A := isCompact_optimal_geodesic_plans v₀ v₁ a.center a.radius_nonneg
    a.left_support a.right_support
  have hQ : ∀ m, IsClosed (Q m) := fun m => isClosed_followsRenyiTree S m a id
  have hfin : ∀ u : Finset ℕ, (A ∩ ⋂ m∈u, Q m).Nonempty := by
    intro u
    obtain ⟨π,hπ,hg,hp,_,hf⟩ := exists_plan_following_renyi_tree S (u.sup id) a
    let v : ProbabilityMeasure C(Time,X) := ⟨π,hπ⟩
    refine ⟨v,⟨hg,hp⟩,mem_iInter.mpr (fun m => mem_iInter.mpr (fun hm => ?_))⟩
    exact hf.of_le (Finset.le_sup (f := id) hm)
  obtain ⟨π,hπ,hf⟩ := hA.inter_iInter_nonempty Q hQ hfin
  exact ⟨π,inferInstance,hπ.1,hπ.2,fun m => mem_iInter.mp hf m⟩

omit [ProperSpace X] in
theorem plan_following_renyi_tree_dyadic_compression {n : ℕ} {K q : ℝ}
    (S : ∀ a : RenyiTransportNode n X, RenyiNodeSplit K q a) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) (hf : ∀ m, FollowsRenyiTree S a (fun t => π.map (fun γ => γ t)) m)
    {t : Time} (ht : t∈⋃ m, dyadicGrid m) :
    π.map (fun γ => γ t) ≤ compressionBudget K n a.distance a.capacity • hausdorff n X := by
  obtain ⟨m,hm⟩ := mem_iUnion.mp ht
  obtain ⟨κ,_,_,_,hc,hκ⟩ := exists_plan_following_renyi_tree S m a
  rw [(hf m).unique_grid hκ t hm]
  exact hc t hm

end RegularPointCoordinates

end

end OAI
