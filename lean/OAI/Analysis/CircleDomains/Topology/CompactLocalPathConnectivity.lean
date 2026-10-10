import OAI.Analysis.CircleDomains.Topology.CompactLocalPaths
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.MetricSpace.Kuratowski

namespace OAI

/-! Local path connectivity of compact locally connected metric spaces,
proved by small ambient approximations in the Kuratowski embedding. -/
open Set Metric Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma compact_subset_locallyPathConnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hK : IsCompact K) [LocallyConnectedSpace K] :
    LocallyPathConnectedSpace K := by
  apply locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mpr
  intro x U hU hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  obtain ⟨δ, hδ, hpaths⟩ := compact_uniform_local_paths hK hε
  apply mem_of_superset (Metric.ball_mem_nhds x hδ)
  intro y hy
  obtain ⟨β, hβK, hβsmall⟩ := hpaths x x.property y y.property (by simpa only [mem_ball, Subtype.dist_eq, dist_comm] using hy)
  let γ : Path x y :=
    { toFun := fun t => ⟨β t, hβK t⟩
      continuous_toFun := β.continuous.subtype_mk _
      source' := Subtype.ext β.source
      target' := Subtype.ext β.target }
  refine ⟨γ, fun t => hball ?_⟩
  exact hβsmall t

lemma compact_metric_locallyPathConnected
    (X : Type*) [MetricSpace X] [CompactSpace X] [LocallyConnectedSpace X] :
    LocallyPathConnectedSpace X := by
  let e : X ≃ₜ range (kuratowskiEmbedding X) :=
    (kuratowskiEmbedding.isometry X).isEmbedding.toHomeomorph
  let : LocallyConnectedSpace (range (kuratowskiEmbedding X)) :=
    e.isQuotientMap.isCoinducing.locallyConnectedSpace
  let : LocallyPathConnectedSpace (range (kuratowskiEmbedding X)) :=
    compact_subset_locallyPathConnected
      (isCompact_range (kuratowskiEmbedding.isometry X).continuous)
  exact e.symm.locallyPathConnectedSpace

lemma compact_metric_connected_open_paths
    (X : Type*) [MetricSpace X] [CompactSpace X] [LocallyConnectedSpace X]
    {U : Set X} (hU : IsOpen U) (hconn : IsConnected U) : IsPathConnected U := by
  let := compact_metric_locallyPathConnected X
  exact hU.isConnected_iff_isPathConnected.mp hconn

end CircleDomainRigidity

end

end OAI
