import OAI.Analysis.CircleDomains.Topology.ConnectedSetPolygonalApproximation

namespace OAI

/-! Uniform local ambient paths near a compact locally connected set.
Their distance to the set can be prescribed independently of their diameter. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma uniform_local_approximate_paths
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) [LocallyConnectedSpace K]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ K, dist x y < δ →
      ∀ η : ℝ, 0 < η → ∃ γ : Path x y,
        (∀ t, dist (γ t) x < ε) ∧ (∀ t, ∃ c ∈ K, dist (γ t) c < η) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨δ, hδ, hlocal⟩ := exists_uniform_small_connected_sets K (show 0 < ε / 3 by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy η hη
  obtain ⟨V, hV, hxV, hyV, hdiam⟩ := hlocal ⟨x, hx⟩ ⟨y, hy⟩ hxy
  have hS : IsConnected (Subtype.val '' V) := hV.image _ continuous_subtype_val.continuousOn
  have hxS : x ∈ Subtype.val '' V := ⟨⟨x, hx⟩, hxV, rfl⟩
  have hyS : y ∈ Subtype.val '' V := ⟨⟨y, hy⟩, hyV, rfl⟩
  obtain ⟨γ, hγ⟩ := connected_set_path_near hS (lt_min hη (show 0 < ε / 3 by linarith)) hxS hyS
  refine ⟨γ, ?_, ?_⟩
  · intro t
    obtain ⟨c, ⟨a, ha, rfl⟩, htc⟩ := hγ t
    have hd := hdiam a ha ⟨x, hx⟩ hxV
    have he := lt_of_lt_of_le htc (min_le_right η (ε / 3))
    have ht := dist_triangle (γ t) (a : E) x
    change dist (a : E) x < ε / 3 at hd
    linarith
  · intro t
    obtain ⟨c, ⟨a, ha, rfl⟩, htc⟩ := hγ t
    exact ⟨a, a.property, htc.trans_le (min_le_left η (ε / 3))⟩

end CircleDomainRigidity

end

end OAI
