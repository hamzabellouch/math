import OAI.Geometry.RCD.Transport.RenyiDyadicData

namespace OAI

/-! # Actual compressed optimal plans with maximal dyadic midpoints

The tree is constructed by genuine midpoint maximization and optimal
matched-path gluing. The density budget is uniform in the tree depth.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.exists_dyadic_renyi_maximizing_plan
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) :
    ∀ (ν₀ ν₁ : Measure X), IsProbabilityMeasure ν₀ → IsProbabilityMeasure ν₁ →
    ∀ (C : ℝ≥0∞), C ≠ ∞ → ν₀ ≤ C • hausdorff n X → ν₁ ≤ C • hausdorff n X →
    ∀ (p : X) (R : ℝ), 0 ≤ R →
    (∀ᵐ x ∂ν₀, dist x p ≤ R) → (∀ᵐ x ∂ν₁, dist x p ≤ R) →
    ∀ (D : ℝ), 0 ≤ D → OptimalPlanDistanceBound ν₀ ν₁ D →
    ∃ π : Measure C(Time,X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧ IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))) ∧
      (∀ t∈dyadicGrid m, π.map (fun γ => γ t) ≤ compressionBudget K n D C • hausdorff n X) ∧
      RenyiDyadicMaximal (hausdorff n X) q (fun t => π.map (fun γ => γ t)) m := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  induction m with
  | zero =>
    intro ν₀ ν₁ hν₀ hν₁ C hC h0 h1 p R hR hs0 hs1 D hD0 _
    let := hν₀
    let := hν₁
    have hm0 := finiteSecondMoment_of_bounded ν₀ p hs0
    have hm1 := finiteSecondMoment_of_bounded ν₁ p hs1
    obtain ⟨π,hπ,hg,hp,_⟩ := hX.cd ν₀ ν₁ hν₀ hν₁
      (Measure.absolutelyContinuous_of_le_smul h0)
      (Measure.absolutelyContinuous_of_le_smul h1) hm0 hm1
    have he := optimalPlan_endpoints ν₀ ν₁ π hp
    have hcap := le_compressionBudget K n D C hn0 hD0
    have h0' : ν₀ ≤ compressionBudget K n D C • hausdorff n X :=
      h0.trans (by intro S; exact mul_le_mul_left hcap _)
    have h1' : ν₁ ≤ compressionBudget K n D C • hausdorff n X :=
      h1.trans (by intro S; exact mul_le_mul_left hcap _)
    refine ⟨π,hπ,hg,hp,?_,trivial⟩
    intro t ht
    rcases ht with rfl | ht
    · rwa [he.1]
    · have ht' : t=1 := ht
      subst t
      rwa [he.2]
  | succ m ih =>
    intro ν₀ ν₁ hν₀ hν₁ C hC h0 h1 p R hR hs0 hs1 D hD0 hD
    let := hν₀
    let := hν₁
    let : Nonempty X := ⟨p⟩
    have hm0 := finiteSecondMoment_of_bounded ν₀ p hs0
    have hm1 := finiteSecondMoment_of_bounded ν₁ p hs1
    obtain ⟨π,hπ,hg,hp,hmidcap,hmax⟩ := hX.exists_global_renyi_midpoint_short K n hn
      ν₀ ν₁ hC h0 h1 p hR hs0 hs1 D hD hq0 hq1
    let := hπ
    let νm := π.map (fun γ => γ midpointTime)
    have hνm : IsProbabilityMeasure νm := inferInstance
    let := hνm
    have he := optimalPlan_endpoints ν₀ ν₁ π hp
    have hp' : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
        (π.map (fun γ => (γ 0,γ 1))) := by rwa [he.1,he.2]
    have hfin := finite_second_moment_cost hm0 hm1 hp.1 hp.2.1
    have hD' : OptimalPlanDistanceBound (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1)) D := by
      rwa [he.1,he.2]
    obtain ⟨hDl,hDr⟩ := OptimalPlanDistanceBound.midpoint_halves π hg hp' hfin hD'
    rw [he.1] at hDl
    rw [he.2] at hDr
    let C' := compressionStep K n D C
    have hC' : C' ≠ ∞ := compressionStep_ne_top K n D hC
    have hincrease : C ≤ C' := le_compressionStep K n D C hn0 hD0
    have h0' : ν₀ ≤ C' • hausdorff n X := h0.trans (by intro S; exact mul_le_mul_left hincrease _)
    have h1' : ν₁ ≤ C' • hausdorff n X := h1.trans (by intro S; exact mul_le_mul_left hincrease _)
    have hm' : νm ≤ C' • hausdorff n X := hmidcap.trans (by
      intro S
      exact mul_le_mul_left (midpointCapacity_le_compressionStep K n D C hn0 hD0) _)
    have hsM : ∀ᵐ x ∂νm, dist x p ≤ 3*R := by
      apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable
        (measurableSet_le (measurable_id.dist measurable_const) measurable_const)).mpr
      exact (optimal_geodesic_plan_bounded ν₀ ν₁ π hg hp p hR hs0 hs1).mono (fun _ h => h.2 midpointTime)
    have hs0' : ∀ᵐ x ∂ν₀, dist x p ≤ 3*R := hs0.mono (fun _ h => by linarith)
    have hs1' : ∀ᵐ x ∂ν₁, dist x p ≤ 3*R := hs1.mono (fun _ h => by linarith)
    obtain ⟨q₀,hq₀,hg₀,hp₀,hgrid₀,htree₀⟩ := ih ν₀ νm hν₀ hνm C' hC' h0' hm'
      p (3*R) (by positivity) hs0' hsM (D/2) (by positivity) hDl
    obtain ⟨q₁,hq₁,hg₁,hp₁,hgrid₁,htree₁⟩ := ih νm ν₁ hνm hν₁ C' hC' hm' h1'
      p (3*R) (by positivity) hsM hs1' (D/2) (by positivity) hDr
    let := hq₀
    let := hq₁
    have he₀ := optimalPlan_endpoints ν₀ νm q₀ hp₀
    have he₁ := optimalPlan_endpoints νm ν₁ q₁ hp₁
    obtain ⟨ρ,hρ,hρ₀,hρ₁⟩ := exists_matched_path_law q₀ q₁ (he₀.2.trans he₁.1.symm)
    let := hρ
    have hp₀' : IsOptimalCoupling (π.map (fun γ => γ 0)) νm
        (q₀.map (fun γ => (γ 0,γ 1))) := by rwa [he.1]
    have hp₁' : IsOptimalCoupling νm (π.map (fun γ => γ 1))
        (q₁.map (fun γ => (γ 0,γ 1))) := by rwa [he.2]
    obtain ⟨hpj,hgj,_⟩ := midpoint_matched_law_optimal π hg hp' hfin
      q₀ q₁ hg₀ hg₁ hp₀' hp₁' ρ hρ₀ hρ₁
    rw [he.1,he.2] at hpj
    refine ⟨ρ.map joinMatched,inferInstance,hgj,hpj,?_,?_⟩
    · intro t ht
      rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
      · rw [joined_law_eval_lowerTime ρ q₀ hρ₀]
        simpa only [show compressionBudget K n (D/2) C' = compressionBudget K n D C from
          compressionBudget_halve K n D C] using hgrid₀ s hs
      · rw [joined_law_eval_upperTime ρ q₁ hρ₁]
        simpa only [show compressionBudget K n (D/2) C' = compressionBudget K n D C from
          compressionBudget_halve K n D C] using hgrid₁ s hs
    · refine ⟨?_,?_,?_⟩
      · intro κ hκ hgκ hpκ
        dsimp only [] at hpκ ⊢
        rw [joined_law_eval_zero ρ q₀ hρ₀,he₀.1,joined_law_eval_one ρ q₁ hρ₁,he₁.2] at hpκ
        rw [joined_law_eval_midpoint ρ q₀ hρ₀,he₀.2]
        exact hmax κ hκ hgκ hpκ
      · exact htree₀.congr (fun t => (joined_law_eval_lowerTime ρ q₀ hρ₀ t).symm)
      · exact htree₁.congr (fun t => (joined_law_eval_upperTime ρ q₁ hρ₁ t).symm)

end RegularPointCoordinates

end

end OAI
