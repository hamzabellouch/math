import OAI.Analysis.CircleDomains.Topology.DiskRayProper
import OAI.Analysis.CircleDomains.Topology.DiskRayTranslates
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

namespace OAI

/-! Each lifted simple disk arc is a proper closed embedding. -/

open Set Function Filter Topology
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem isProperMap_diskRayLift {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet) :
    IsProperMap (diskRayLift γ hγ.1 hγ.2.2.1) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨(diskRayLift γ hγ.1 hγ.2.2.1).continuous, ?_⟩
  intro Q hQ
  obtain ⟨Y, hY⟩ := (hQ.image continuous_snd).bddAbove
  obtain ⟨c, _, hc, htail⟩ := compact_disk_rays_depth_escape {γ} isCompact_singleton
    (by simpa only [singleton_subset_iff] using hγ) Y
  let E : {t : PathTime // t ≤ c} → DiskRayTime :=
    fun t => ⟨t.val, t.property.trans_lt hc⟩
  have hE : Continuous E := continuous_subtype_val.subtype_mk _
  let : CompactSpace {t : PathTime // t ≤ c} := isCompact_iff_compactSpace.mp isClosed_Iic.isCompact
  have hcomp : IsCompact (range E) := isCompact_range hE
  apply hcomp.of_isClosed_subset
    (hQ.isClosed.preimage (diskRayLift γ hγ.1 hγ.2.2.1).continuous)
  intro t ht
  have hd : diskRayDepth γ t ≤ Y := hY (mem_image_of_mem Prod.snd ht)
  have htc : t.val ≤ c := by
    by_contra! hh
    exact (not_lt_of_ge hd) (htail γ (mem_singleton γ) t hh.le)
  exact ⟨⟨t.val, htc⟩, rfl⟩

theorem isClosedEmbedding_diskRayLift {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet) :
    IsClosedEmbedding (diskRayLift γ hγ.1 hγ.2.2.1) :=
  .of_continuous_injective_isClosedMap (diskRayLift γ hγ.1 hγ.2.2.1).continuous
    (diskRayLift_injective γ hγ.1 hγ.2.2.1) (isProperMap_diskRayLift hγ).isClosedMap

theorem isClosed_range_diskRayLift {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet) :
    IsClosed (range (diskRayLift γ hγ.1 hγ.2.2.1)) :=
  (isClosedEmbedding_diskRayLift hγ).isClosed_range

end CircleDomainRigidity

end

end OAI
