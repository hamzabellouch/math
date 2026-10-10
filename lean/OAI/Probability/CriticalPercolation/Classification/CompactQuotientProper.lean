import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.CompactDiscreteQuotient

namespace OAI

section
noncomputable section
open Set Function Topology

namespace CriticalPercolation.CompactQuotient
variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
variable (H : Subgroup A) [H.Normal]

lemma proper_mk_of_compact (hH : IsCompact (H : Set A)) :
    IsProperMap (QuotientGroup.mk' H) := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  exact ⟨QuotientGroup.continuous_mk,QuotientGroup.isClosedMap_coe hH,
    fun q => compact_preimage_of_finite H hH {q} (Set.finite_singleton q)⟩

lemma locallyCompact_of_compact_kernel (hH : IsCompact (H : Set A))
    [LocallyCompactSpace (A ⧸ H)] : LocallyCompactSpace A := by
  obtain ⟨K,hK,hK1⟩ := exists_compact_mem_nhds (QuotientGroup.mk' H (1 : A))
  exact ((proper_mk_of_compact H hH).isCompact_preimage hK).locallyCompactSpace_of_mem_nhds_of_group
    (QuotientGroup.continuous_mk.continuousAt hK1)

end CriticalPercolation.CompactQuotient
end
end

end OAI
