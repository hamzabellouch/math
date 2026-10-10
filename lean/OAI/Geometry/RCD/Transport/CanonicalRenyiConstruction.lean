import OAI.Geometry.RCD.Transport.CanonicalRenyiTree

namespace OAI

/-! # Realization of every finite level of the fixed midpoint tree -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem exists_plan_following_renyi_tree {n : ℕ} {K q : ℝ}
    (S : ∀ a : RenyiTransportNode n X, RenyiNodeSplit K q a) (m : ℕ) :
    ∀ a : RenyiTransportNode n X,
    ∃ π : Measure C(Time,X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧ IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))) ∧
      (∀ t∈dyadicGrid m, π.map (fun γ => γ t) ≤
        compressionBudget K n a.distance a.capacity • hausdorff n X) ∧
      FollowsRenyiTree S a (fun t => π.map (fun γ => γ t)) m := by
  induction m with
  | zero =>
    intro a
    let s := S a
    have he := optimalPlan_endpoints a.left a.right s.plan s.optimal
    have hcap := le_compressionBudget K n a.distance a.capacity (Nat.cast_nonneg n) a.distance_nonneg
    refine ⟨s.plan,s.probability,s.geodesic,s.optimal,?_,he⟩
    intro t ht
    rcases ht with rfl | ht
    · rw [he.1]
      exact a.left_bound.trans (by intro B; exact mul_le_mul_left hcap _)
    · have ht' : t=1 := ht
      subst t
      rw [he.2]
      exact a.right_bound.trans (by intro B; exact mul_le_mul_left hcap _)
  | succ m ih =>
    intro a
    let : Nonempty X := ⟨a.center⟩
    let s := S a
    let := s.probability
    let b := s.leftNode
    let c := s.rightNode
    obtain ⟨π₀,hπ₀,hg₀,hp₀,hcap₀,hf₀⟩ := ih b
    obtain ⟨π₁,hπ₁,hg₁,hp₁,hcap₁,hf₁⟩ := ih c
    let := hπ₀
    let := hπ₁
    have he₀ := optimalPlan_endpoints b.left b.right π₀ hp₀
    have he₁ := optimalPlan_endpoints c.left c.right π₁ hp₁
    have hbc : b.right=c.left := rfl
    obtain ⟨ρ,hρ,hρ₀,hρ₁⟩ := exists_matched_path_law π₀ π₁ (he₀.2.trans (hbc.trans he₁.1.symm))
    let := hρ
    have he := optimalPlan_endpoints a.left a.right s.plan s.optimal
    have hp : IsOptimalCoupling (s.plan.map (fun γ => γ 0)) (s.plan.map (fun γ => γ 1))
        (s.plan.map (fun γ => (γ 0,γ 1))) := by
      rw [he.1,he.2]
      exact s.optimal
    let := a.left_probability
    let := a.right_probability
    have hm0 := finiteSecondMoment_of_bounded a.left a.center a.left_support
    have hm1 := finiteSecondMoment_of_bounded a.right a.center a.right_support
    have hfin := finite_second_moment_cost hm0 hm1 s.optimal.1 s.optimal.2.1
    have hp₀' : IsOptimalCoupling (s.plan.map (fun γ => γ 0))
        (s.plan.map (fun γ => γ midpointTime)) (π₀.map (fun γ => (γ 0,γ 1))) := by
      rw [he.1]
      exact hp₀
    have hp₁' : IsOptimalCoupling (s.plan.map (fun γ => γ midpointTime))
        (s.plan.map (fun γ => γ 1)) (π₁.map (fun γ => (γ 0,γ 1))) := by
      rw [he.2]
      exact hp₁
    obtain ⟨hpj,hgj,_⟩ := midpoint_matched_law_optimal s.plan s.geodesic hp hfin
      π₀ π₁ hg₀ hg₁ hp₀' hp₁' ρ hρ₀ hρ₁
    rw [he.1,he.2] at hpj
    refine ⟨ρ.map joinMatched,inferInstance,hgj,hpj,?_,?_,?_,?_,?_,?_⟩
    · intro t ht
      rcases ht with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
      · rw [joined_law_eval_lowerTime ρ π₀ hρ₀]
        have hc := hcap₀ u hu
        change π₀.map (fun γ => γ u) ≤
          compressionBudget K n (a.distance/2) (compressionStep K n a.distance a.capacity) •
            hausdorff n X at hc
        rwa [compressionBudget_halve] at hc
      · rw [joined_law_eval_upperTime ρ π₁ hρ₁]
        have hc := hcap₁ u hu
        change π₁.map (fun γ => γ u) ≤
          compressionBudget K n (a.distance/2) (compressionStep K n a.distance a.capacity) •
            hausdorff n X at hc
        rwa [compressionBudget_halve] at hc
    · exact (joined_law_eval_zero ρ π₀ hρ₀).trans he₀.1
    · exact (joined_law_eval_one ρ π₁ hρ₁).trans he₁.2
    · exact (joined_law_eval_midpoint ρ π₀ hρ₀).trans he₀.2
    · exact hf₀.congr (fun t => (joined_law_eval_lowerTime ρ π₀ hρ₀ t).symm)
    · exact hf₁.congr (fun t => (joined_law_eval_upperTime ρ π₁ hρ₁ t).symm)

end RegularPointCoordinates

end

end OAI
