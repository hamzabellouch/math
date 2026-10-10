import OAI.Geometry.RCD.Transport.OptimalAveragePlan

namespace OAI

/-! # Transferring a fixed initial speed from one optimizer to another

The common initial marginal identifies the slope-square integral. Equality
of optimal costs then turns the pointwise speed bound into equality, even
when the second plan has no compression estimate.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem optimal_initial_speed_transfer {ν₀ ν₁ : Measure X}
    (π ρ : Measure C(Time,X)) [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hr : IsOptimalCoupling ν₀ ν₁ (ρ.map (fun γ => (γ 0,γ 1))))
    (hip : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) π)
    (hir : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) ρ)
    (G : X → ℝ) (hG : Measurable G)
    (hgp : ∀ᵐ γ ∂π, G (γ 0)=dist (γ 0) (γ 1))
    (hgn : ∀ᵐ γ ∂ρ, 0≤G (γ 0))
    (hgr : ∀ᵐ γ ∂ρ, G (γ 0)≤dist (γ 0) (γ 1)) :
    ∀ᵐ γ ∂ρ, G (γ 0)=dist (γ 0) (γ 1) := by
  have hiG : Integrable (fun γ : C(Time,X) => G (γ 0)^2) ρ := by
    apply hir.mono' ((hG.comp (measurable_path_eval 0)).pow_const 2).aestronglyMeasurable
    filter_upwards [hgn,hgr] with γ h0 hle
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq₀ h0 dist_nonneg |>.mpr hle
  have hsame : (∫ γ, G (γ 0)^2 ∂π)=(∫ γ, G (γ 0)^2 ∂ρ) := by
    rw [←integral_map (measurable_path_eval 0).aemeasurable (hG.pow_const 2).aestronglyMeasurable,
      ←integral_map (measurable_path_eval 0).aemeasurable (hG.pow_const 2).aestronglyMeasurable,
      (optimalPlan_endpoints ν₀ ν₁ π hp).1,(optimalPlan_endpoints ν₀ ν₁ ρ hr).1]
  have hcost : (∫ γ, dist (γ 0) (γ 1)^2 ∂π)=(∫ γ, dist (γ 0) (γ 1)^2 ∂ρ) :=
    (optimal_plan_cost_real hp hip).symm.trans (optimal_plan_cost_real hr hir)
  have hs : ∀ᵐ γ ∂ρ, 0≤dist (γ 0) (γ 1)^2-G (γ 0)^2 := by
    filter_upwards [hgn,hgr] with γ h0 hle
    exact sub_nonneg.mpr (sq_le_sq₀ h0 dist_nonneg |>.mpr hle)
  have hz : (∫ γ, dist (γ 0) (γ 1)^2-G (γ 0)^2 ∂ρ)=0 := by
    rw [integral_sub hir hiG,←hcost,←hsame]
    have he : (∫ γ, G (γ 0)^2 ∂π)=(∫ γ, dist (γ 0) (γ 1)^2 ∂π) :=
      integral_congr_ae (hgp.mono (fun γ hγ => congrArg (fun x : ℝ => x^2) hγ))
    rw [he,sub_self]
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hs (hir.sub hiG)).mp hz,hgn] with γ hγ hn
  change dist (γ 0) (γ 1)^2-G (γ 0)^2=0 at hγ
  exact (sq_eq_sq₀ hn dist_nonneg).mp (by linarith)

end RegularPointCoordinates

end

end OAI
