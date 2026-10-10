import OAI.Geometry.RCD.Transport.OptimalSpeedTransfer
import OAI.Geometry.RCD.Transport.RenyiTransportNode

namespace OAI

/-! # Common initial length of two optimal plans

Only the reference optimizer needs bounded compression. A potential for
the average coupling bounds the speed on both optimizers. The
Sobolev speed identity and equality of costs make both bounds equalities.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.common_optimal_initial_length
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (a : RenyiTransportNode n X) (π ρ : Measure C(Time,X))
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (hgπ : ∀ᵐ γ ∂π, IsGeodesic γ) (hgρ : ∀ᵐ γ ∂ρ, IsGeodesic γ)
    (hpπ : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    (hpρ : IsOptimalCoupling a.left a.right (ρ.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X) :
    ∃ G : X → ℝ, Measurable G ∧
      (∀ᵐ γ ∂π, G (γ 0)=dist (γ 0) (γ 1)) ∧
      ∀ᵐ γ ∂ρ, G (γ 0)=dist (γ 0) (γ 1) := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let : IsProbabilityMeasure a.left := a.left_probability
  let : IsProbabilityMeasure a.right := a.right_probability
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hac : a.left ≪ μ := Measure.absolutelyContinuous_of_le_smul a.left_bound
  obtain ⟨τ,hτ,_,hpτ,hπac,hρac⟩ := optimalPlan_average π ρ hgπ hgρ hpπ hpρ
  let := hτ
  obtain ⟨u,φ,ψ,L,_,_,_,_,hu,had,hct,hbt⟩ := hpτ.bounded_sobolev_potential
    μ hX.quadratic hX.geodesic a.left a.right hac a.center a.radius_nonneg a.left_support a.right_support
  have hm : Measurable (fun γ : C(Time,X) => (γ 0,γ 1)) :=
    (measurable_path_eval 0).prodMk (measurable_path_eval 1)
  have hct' := ae_of_ae_map hm.aemeasurable hct
  have hbt' := ae_of_ae_map hm.aemeasurable hbt
  let G := SobolevSpace.minimalSlope μ hX.quadratic u
  have hip := optimalPlan_dist_sq_integrable a.left a.right π hpπ a.center
    (integrable_dist_sq_of_ae_bounded a.left a.center a.left_support)
    (integrable_dist_sq_of_ae_bounded a.right a.center a.right_support)
  have hir := optimalPlan_dist_sq_integrable a.left a.right ρ hpρ a.center
    (integrable_dist_sq_of_ae_bounded a.left a.center a.left_support)
    (integrable_dist_sq_of_ae_bounded a.right a.center a.right_support)
  have hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π :=
    (memLp_two_iff_integrable_sq ((measurable_path_eval 0).dist
      (measurable_path_eval 1)).aestronglyMeasurable).mpr hip
  have hgp : ∀ᵐ γ ∂π, G (γ 0)=dist (γ 0) (γ 1) :=
    (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic u).kantorovich_gradient_eq_displacement
      μ π hgπ hC hcomp hD hu had (hct'.filter_mono hπac.ae_le) (hbt'.filter_mono hπac.ae_le)
  have hnn : ∀ᵐ γ ∂ρ, 0≤G (γ 0) := by
    have hnμ : ∀ᵐ x ∂μ, 0≤G x := (Lp.coeFn_nonneg G).mpr
      (SobolevSpace.minimalSlope_nonneg μ hX.quadratic u)
    have hn0 := hnμ.filter_mono hac.ae_le
    rw [←(optimalPlan_endpoints a.left a.right ρ hpρ).1] at hn0
    exact ae_of_ae_map (measurable_path_eval 0).aemeasurable hn0
  exact ⟨G,(Lp.stronglyMeasurable G).measurable,hgp,
    optimal_initial_speed_transfer π ρ hpπ hpρ hip hir G (Lp.stronglyMeasurable G).measurable
      hgp hnn (hbt'.filter_mono hρac.ae_le)⟩

end RegularPointCoordinates

end

end OAI
