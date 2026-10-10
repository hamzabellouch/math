import OAI.Probability.SLE.Geometry.EndpointClusterInterval
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! A bounded continuous real path has an endpoint limit when its cluster
values contain no nontrivial interval. -/
noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge

theorem exists_endpoint_limit_of_no_cluster_interval {f : ℝ → ℝ} {D : ℝ}
    (hD : 0<D) (hC : ContinuousOn f (Ioo 0 D)) {K : Set ℝ} (hK : IsCompact K)
    (hmem : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), f t∈K)
    (hno : ∀ a b : ℝ, a<b → ¬ ∀ c∈Ioo a b, MapClusterPt c (𝓝[>] (0:ℝ)) f) :
    ∃ a∈K, Tendsto f (𝓝[>] (0:ℝ)) (𝓝 a) := by
  obtain ⟨a,haK,ha⟩ := hK.exists_mapClusterPt (tendsto_principal.mpr hmem)
  refine ⟨a,haK,hK.tendsto_nhds_of_unique_mapClusterPt hmem ?_⟩
  intro b _ hb
  by_contra hba
  rcases lt_or_gt_of_ne hba with hlt | hgt
  · exact hno b a hlt (endpoint_cluster_interval hD hC hb ha)
  · exact hno a b hgt (endpoint_cluster_interval hD hC ha hb)

end SLEExactGauge

end

end OAI
