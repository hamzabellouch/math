import OAI.Geometry.RCD.Transport.StrongReduced
import OAI.Geometry.RCD.Transport.CompressedSubplanNode

namespace OAI

/-! # Every normalized nonzero subplan satisfies the exact reduced bound -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem normalized_subplan_reduced (hn : 2 ≤ n) (hK : K ≤ 0)
    {N : ℝ} (hN : (n:ℝ) ≤ N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X)
    (κ : Measure C(Time,X)) (hk : κ ≤ π) (hk0 : κ univ ≠ 0) :
    ∀ t, ReducedRenyiChordBound (hausdorff n X) K N ((κ univ)⁻¹ • κ) t := by
  let := a.left_probability
  let := a.right_probability
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hk
  have hd := a.distance_bound π inferInstance hg hp
  obtain ⟨b,hb₀,hb₁,_⟩ := hX.compressed_subplan_node K n hn a π hg hp hC hc κ hk hk0
    a.distance_nonneg (hd.filter_mono hk.absolutelyContinuous.ae_le)
  have he := optimalPlan_endpoints a.left a.right π hp
  have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))) := by rwa [he.1,he.2]
  have hfin := coupling_transportCost_ne_top hp.1 hp.2.1 a.center
    (integrable_dist_sq_of_ae_bounded _ a.center a.left_support)
    (integrable_dist_sq_of_ae_bounded _ a.center a.right_support)
  let ρ := (κ univ)⁻¹ • κ
  obtain ⟨hρ,hgρ,hpρ,_⟩ := normalized_optimal_subplan π hg hpp hfin κ hk hk0
  let : IsProbabilityMeasure ρ := hρ
  have heρ (t : Time) : ρ.map (fun γ => γ t)=(κ univ)⁻¹ • κ.map (fun γ => γ t) :=
    Measure.map_smul _ (measurable_path_eval t).aemeasurable
  have hpρ' : IsOptimalCoupling b.left b.right (ρ.map (fun γ => (γ 0,γ 1))) := by
    rw [hb₀,hb₁,←heρ,←heρ]
    exact hpρ
  exact hX.all_compressed_reduced_interpolation hn hK hN b ρ hgρ hpρ'
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hk0) hC)
    (normalized_subplan_compression π κ hk hc)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
