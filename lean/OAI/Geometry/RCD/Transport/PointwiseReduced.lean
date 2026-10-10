import OAI.Geometry.RCD.Transport.UnnormalizedReduced
import OAI.Geometry.RCD.Transport.CompressedSubplanDensity
import OAI.Geometry.RCD.Transport.EndpointChordLimit
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

namespace OAI

/-! # Pointwise reduced density interpolation along the actual optimal plan

Every measurable path restriction has the reduced integral bound. All of its
marginal densities agree with the original densities along that restriction,
so localization gives the pointwise inequality without a Jensen reversal.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem pointwise_reduced_interpolation (hn : 2 ≤ n) (hK : K ≤ 0)
    {N : ℝ} (hN : (n:ℝ) ≤ N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (t : Time) :
    ∀ᵐ γ ∂π,
      sigma K (N+1) (1-(t:ℝ)) (dist (γ 0) (γ 1))*
        ((π.map (fun γ => γ 0)).rnDeriv (hausdorff n X) (γ 0))^(-(1/N))+
      sigma K (N+1) (t:ℝ) (dist (γ 0) (γ 1))*
        ((π.map (fun γ => γ 1)).rnDeriv (hausdorff n X) (γ 1))^(-(1/N)) ≤
      ((π.map (fun γ => γ t)).rnDeriv (hausdorff n X) (γ t))^(-(1/N)) := by
  let μ := hausdorff n X
  have hN1 : 1 < N := by
    have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hNp : 1 < N+1 := by linarith
  let F := fun γ : C(Time,X) =>
    sigma K (N+1) (1-(t:ℝ)) (dist (γ 0) (γ 1))*
      ((π.map (fun γ => γ 0)).rnDeriv μ (γ 0))^(-(1/N))+
    sigma K (N+1) (t:ℝ) (dist (γ 0) (γ 1))*
      ((π.map (fun γ => γ 1)).rnDeriv μ (γ 1))^(-(1/N))
  let G := fun γ : C(Time,X) => ((π.map (fun γ => γ t)).rnDeriv μ (γ t))^(-(1/N))
  have hm (s : Time) : Measurable (fun γ : C(Time,X) =>
      ((π.map (fun γ => γ s)).rnDeriv μ (γ s))^(-(1/N))) :=
    (((π.map (fun γ => γ s)).measurable_rnDeriv μ).comp (measurable_path_eval s)).pow_const _
  have hF : Measurable F :=
    ((measurable_path_sigma_nonpos hK hNp (sub_nonneg.mpr t.property.2)
      (by linarith [t.property.1])).mul (hm 0)).add
    ((measurable_path_sigma_nonpos hK hNp t.property.1 t.property.2).mul (hm 1))
  have he := optimalPlan_endpoints a.left a.right π hp
  have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))) := by rwa [he.1,he.2]
  have hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x a.center ≤ a.radius := by rw [he.1]; exact a.left_support
  have hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x a.center ≤ a.radius := by rw [he.2]; exact a.right_support
  change F ≤ᵐ[π] G
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hF
  intro S hS _
  by_cases hz : π S=0
  · have hr : π.restrict S=0 := Measure.restrict_eq_zero.mpr hz
    rw [hr]
    simp
  let κ := π.restrict S
  have hk0 : κ univ ≠ 0 := by simpa only [κ,Measure.restrict_apply_univ] using hz
  have hden (s : Time) : ∀ᵐ γ ∂κ,
      (κ.map (fun γ => γ s)).rnDeriv μ (γ s)=(π.map (fun γ => γ s)).rnDeriv μ (γ s) :=
    hX.restricted_plan_density hn a.center a.radius_nonneg π hg hpp hC hc hs₀ hs₁ hS s
  have hbound := hX.subplan_reduced hn hK hN a π hg hp ENNReal.ofReal_ne_top hc
    κ Measure.restrict_le_self hk0 t
  unfold ReducedRenyiChordBound at hbound
  have hlhs : (∫⁻ γ, sigma K (N+1) (1-(t:ℝ)) (dist (γ 0) (γ 1))*
      ((κ.map (fun γ => γ 0)).rnDeriv μ (γ 0))^(-(1/N))+
      sigma K (N+1) (t:ℝ) (dist (γ 0) (γ 1))*
      ((κ.map (fun γ => γ 1)).rnDeriv μ (γ 1))^(-(1/N)) ∂κ) = ∫⁻ γ, F γ ∂κ := by
    apply lintegral_congr_ae
    filter_upwards [hden 0,hden 1] with γ hγ₀ hγ₁
    rw [hγ₀,hγ₁]
  have hrhs : renyiIntegral μ (κ.map (fun γ => γ t)) N=∫⁻ γ, G γ ∂κ := by
    rw [renyiIntegral_eq_inverse_density μ _
      ((Measure.map_mono Measure.restrict_le_self (measurable_path_eval t)).absolutelyContinuous.trans
        (Measure.absolutelyContinuous_of_le_smul (hc t))) hN1,
      lintegral_map (((κ.map (fun γ => γ t)).measurable_rnDeriv μ).pow_const _)
        (measurable_path_eval t)]
    apply lintegral_congr_ae
    exact (hden t).mono fun γ hγ => congrArg (fun r : ℝ≥0∞ => r^(-(1/N))) hγ
  rw [hlhs,hrhs] at hbound
  exact hbound

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
