import OAI.Geometry.RCD.Heat.GaussianMidpoint

namespace OAI

/-! # The Gaussian entropy-power midpoint estimate on every transport subinterval -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem gaussian_entropy_midpoint_subinterval (hn : 2 ≤ n) (hK : K ≤ 0)
    {N : ℝ} (hN : (n:ℝ) ≤ N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (s t : Time) :
    Real.exp (K*|(s:ℝ)-(t:ℝ)|^2*(wassersteinSq a.left a.right).toReal/(8*N))*
      (Real.exp (-(boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ s)))/N)+
        Real.exp (-(boltzmannEntropy (hausdorff n X) (π.map (fun γ => γ t)))/N))/2 ≤
      Real.exp (-(boltzmannEntropy (hausdorff n X)
        (π.map (fun γ => γ (timeSegment s t midpointTime))))/N) := by
  let : CompleteSpace X := hX.complete
  let : Nonempty X := ⟨a.center⟩
  let := a.left_probability
  let := a.right_probability
  have he := optimalPlan_endpoints a.left a.right π hp
  have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))) := by rwa [he.1,he.2]
  have hfin := coupling_transportCost_ne_top hp.1 hp.2.1 a.center
    (integrable_dist_sq_of_ae_bounded _ a.center a.left_support)
    (integrable_dist_sq_of_ae_bounded _ a.center a.right_support)
  obtain ⟨_,hgρ,hpρ⟩ := geodesic_subpath_law π hg hpp hfin s t
  let ρ := π.map (subpath s t)
  have heval (u : Time) : ρ.map (fun γ => γ u)=π.map (fun γ => γ (timeSegment s t u)) := subpath_map_eval π s t u
  have hcρ (u : Time) : ρ.map (fun γ => γ u) ≤ ENNReal.ofReal C • hausdorff n X := by
    rw [heval]; exact hc _
  have hstay (u : Time) : ∀ᵐ x ∂π.map (fun γ => γ u), dist x a.center ≤ 3*a.radius := by
    apply (ae_map_iff (measurable_path_eval u).aemeasurable
      (measurableSet_le (continuous_id.dist continuous_const).measurable measurable_const)).mpr
    exact (optimal_geodesic_plan_bounded _ _ π hg hp a.center a.radius_nonneg
      a.left_support a.right_support).mono fun γ hγ => hγ.2 u
  have hs₀ : ∀ᵐ x ∂ρ.map (fun γ => γ 0), dist x a.center ≤ 3*a.radius := by
    rw [heval,timeSegment_zero]; exact hstay s
  have hs₁ : ∀ᵐ x ∂ρ.map (fun γ => γ 1), dist x a.center ≤ 3*a.radius := by
    rw [heval,timeSegment_one]; exact hstay t
  let b : RenyiTransportNode n X :=
    ⟨ρ.map (fun γ => γ 0),ρ.map (fun γ => γ 1),inferInstance,inferInstance,
      a.center,3*a.radius,mul_nonneg (by norm_num) a.radius_nonneg,hs₀,hs₁,ENNReal.ofReal C,ENNReal.ofReal_ne_top,
      hcρ 0,hcρ 1,2*(3*a.radius),mul_nonneg (by norm_num) (mul_nonneg (by norm_num) a.radius_nonneg),
      optimalPlanDistanceBound_of_bounded _ _ a.center hs₀ hs₁⟩
  have hpρ' : IsOptimalCoupling b.left b.right (ρ.map (fun γ => (γ 0,γ 1))) := by
    simpa only [b,heval,timeSegment_zero,timeSegment_one] using hpρ
  have hh := hX.gaussian_midpoint_entropy_power hn hK hN b ρ hgρ hpρ' hC hcρ
  have hw : (wassersteinSq b.left b.right).toReal=
      |(s:ℝ)-(t:ℝ)|^2*(wassersteinSq a.left a.right).toReal := by
    change (wassersteinSq (ρ.map (fun γ => γ 0)) (ρ.map (fun γ => γ 1))).toReal=_
    rw [heval,heval,timeSegment_zero,timeSegment_one,
      wassersteinSq_eq_cost (geodesic_plan_optimal_marginals π hg hpp hfin s t),
      geodesic_plan_cost π hg,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),wassersteinSq_eq_cost hp]
  rw [hw] at hh
  change Real.exp (K*(|(s:ℝ)-(t:ℝ)|^2*(wassersteinSq a.left a.right).toReal)/(8*N))*
    (Real.exp (-(boltzmannEntropy (hausdorff n X) (ρ.map (fun γ => γ 0)))/N)+
      Real.exp (-(boltzmannEntropy (hausdorff n X) (ρ.map (fun γ => γ 1)))/N))/2 ≤ _ at hh
  simp only [heval,timeSegment_zero,timeSegment_one] at hh
  simpa only [mul_assoc] using hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
