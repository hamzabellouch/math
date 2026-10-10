import OAI.Geometry.RCD.Transport.OptimalInitialLength
import OAI.Geometry.RCD.Transport.OptimalSubmeasureLength

namespace OAI

/-! # Endpoint preservation of length classes for optimal submeasures

Compression of the reference plan gives its initial Kantorovich speed.
Thus the initial component marginal already fixes every measurable length
class, without prescribing an interior marginal of the competitor.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.optimal_initial_submeasure_length_transfer
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (a : RenyiTransportNode n X) (π ρ : Measure C(Time,X))
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (hgπ : ∀ᵐ γ ∂π, IsGeodesic γ) (hgρ : ∀ᵐ γ ∂ρ, IsGeodesic γ)
    (hpπ : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    (hpρ : IsOptimalCoupling a.left a.right (ρ.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hc : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    (η ζ : Measure C(Time,X)) (hη : η≤π) (hζ : ζ≤ρ)
    (he : η.map (fun γ => γ 0)=ζ.map (fun γ => γ 0))
    {S : Set ℝ} (hS : MeasurableSet S)
    (hηS : ∀ᵐ γ ∂η, dist (γ 0) (γ 1)∈S) :
    ∀ᵐ γ ∂ζ, dist (γ 0) (γ 1)∈S := by
  obtain ⟨G,hG,hGπ,hGρ⟩ := hX.common_optimal_initial_length K n hn a π ρ hgπ hgρ hpπ hpρ hC hc
  have hGη := hGπ.filter_mono hη.absolutelyContinuous.ae_le
  have hGζ := hGρ.filter_mono hζ.absolutelyContinuous.ae_le
  have heη : ∀ᵐ x ∂η.map (fun γ => γ 0), G x∈S := by
    apply (ae_map_iff (measurable_path_eval 0).aemeasurable (hS.preimage hG)).mpr
    filter_upwards [hGη,hηS] with γ hγ hγS
    rwa [hγ]
  rw [he] at heη
  have heζ := ae_of_ae_map (measurable_path_eval 0).aemeasurable heη
  filter_upwards [hGζ,heζ] with γ hγ hγS
  rwa [←hγ]

theorem NoncollapsedRCD.compressed_optimal_distance_bound
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (a : RenyiTransportNode n X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hc : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    {D : ℝ} (hD : ∀ᵐ γ ∂π, dist (γ 0) (γ 1)≤D) :
    OptimalPlanDistanceBound a.left a.right D := by
  intro ρ hρ hgρ hpρ
  let := hρ
  have heπ := optimalPlan_endpoints a.left a.right π hp
  have heρ := optimalPlan_endpoints a.left a.right ρ hpρ
  exact hX.optimal_initial_submeasure_length_transfer K n hn a π ρ hg hgρ hp hpρ hC hc
    π ρ le_rfl le_rfl (heπ.1.trans heρ.1.symm) measurableSet_Iic hD

end RegularPointCoordinates

end

end OAI
