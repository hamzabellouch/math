import OAI.Geometry.RCD.Transport.PlanEndpointComparison

namespace OAI

/-! # Pointwise action comparison from compressed small-ball plans -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.pointwise_comparison_of_plans {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (z : X)
    (F G : X → ℝ) (hF : Measurable F) (hG : Measurable G) {T : ℝ} (hT : 0 < T)
    (hLip : ∀ r : ℝ, 0 < r → ∃ L : ℝ≥0,
      LipschitzOnWith L F (closedBall z r) ∧ LipschitzOnWith L G (closedBall z r))
    (hplan : ∀ r : ℝ, 0 < r → ∀ (π : Measure C(Time,X)) [IsProbabilityMeasure π],
      (∀ᵐ γ ∂π, IsGeodesic γ) →
      ∀ C : ℝ≥0∞, C ≠ ∞ →
      (∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X) →
      MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π →
      (∀ t : Time, ∀ᵐ γ ∂π, γ t ∈ closedBall z r) →
      (∫ γ : C(Time,X), F (γ 0) ∂π)-(∫ γ : C(Time,X), G (γ 1) ∂π) ≤
        (∫ γ : C(Time,X), (dist (γ 0) (γ 1))^2 ∂π)/(2*T))
    (x y : X) : F x-G y ≤ (dist x y)^2/(2*T) := by
  let r := dist x z+3*(dist x y+1)+1
  have hr : 0 < r := by dsimp only [r]; positivity
  have hx : x ∈ closedBall z r := by
    change dist x z ≤ r
    dsimp only [r]
    linarith [dist_nonneg (x := x) (y := y)]
  have hy : y ∈ closedBall z r := by
    change dist y z ≤ r
    have hh := dist_triangle y x z
    rw [dist_comm y x] at hh
    dsimp only [r]
    linarith [dist_nonneg (x := x) (y := y)]
  obtain ⟨L,hLF,hLG⟩ := hLip r hr
  have hb (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
      F x-G y ≤ (dist x y+2*ρ)^2/(2*T)+2*(L:ℝ)*ρ := by
    obtain ⟨π,hπ,C,hC,hgeo,hLength,hcomp,hnear⟩ := hX.nearby_ball_plan hn x y hρ
    let := hπ
    have hstay (t : Time) : ∀ᵐ γ ∂π, γ t ∈ closedBall z r := by
      filter_upwards [hnear] with γ hγ
      change dist (γ t) z ≤ r
      have hh := dist_triangle (γ t) x z
      have ht := hγ.2.2 t
      dsimp only [r]
      linarith
    have hvalue₀ := plan_endpoint_lipschitz_error π F hF hLF x hx 0
      (by
        filter_upwards [hnear,hstay 0] with γ hγ hs
        exact ⟨hs,hγ.1⟩)
    have hvalue₁ := plan_endpoint_lipschitz_error π G hG hLG y hy 1
      (by
        filter_upwards [hnear,hstay 1] with γ hγ hs
        exact ⟨hs,hγ.2.1⟩)
    have hcost := endpoint_ball_plan_cost_bound π hLength x y
      (hnear.mono fun γ hγ => ⟨hγ.1,hγ.2.1⟩)
    have hcmp := (hplan r hr π hgeo C hC hcomp hLength hstay).trans
      (div_le_div_of_nonneg_right hcost (by positivity : 0 ≤ 2*T))
    have h0 := (abs_le.mp hvalue₀).1
    have h1 := (abs_le.mp hvalue₁).2
    linarith
  have hc : ContinuousAt (fun ρ : ℝ => (dist x y+2*ρ)^2/(2*T)+2*(L:ℝ)*ρ) 0 := by fun_prop
  have hl : Tendsto (fun ρ : ℝ => (dist x y+2*ρ)^2/(2*T)+2*(L:ℝ)*ρ)
      (𝓝[>] 0) (𝓝 ((dist x y)^2/(2*T))) := by
    simpa only [mul_zero,add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hl
  have hsmall : ∀ᶠ ρ in 𝓝[>] (0:ℝ), ρ < 1 :=
    (gt_mem_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hsmall] with ρ hρ hρ1
  exact hb ρ hρ hρ1.le

end RegularPointCoordinates

end

end OAI
