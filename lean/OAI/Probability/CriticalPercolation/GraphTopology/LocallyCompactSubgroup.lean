import Mathlib
import OAI.Probability.CriticalPercolation.Classification.CompactQuotientProper

namespace OAI

section
noncomputable section
open Set Function Topology Filter

namespace CriticalPercolation.CompactQuotient
variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]

lemma closed_of_locallyCompact_subgroup (L : Subgroup A) [LocallyCompactSpace L] :
    IsClosed (L : Set A) := by
  let _ : UniformSpace A := IsTopologicalGroup.rightUniformSpace A
  have hright : IsRightUniformGroup L := by
    refine {uniformity_eq := ?_}
    change Filter.comap (fun p : L × L => ((p.1 : A),(p.2 : A)))
      (Filter.comap (fun p : A × A => p.2*p.1⁻¹) (𝓝 (1 : A))) =
      Filter.comap (fun p : L × L => p.2*p.1⁻¹) (𝓝 (1 : L))
    rw [nhds_subtype_eq_comap,Filter.comap_comap,Filter.comap_comap]
    rfl
  let _ := hright
  let _ : CompleteSpace L := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace L
  exact (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace L)).isClosed

lemma closed_of_compact_kernel_locallyCompact_quotient
    (L : Subgroup A) (H : Subgroup L) [H.Normal]
    (hH : IsCompact (H : Set L)) [LocallyCompactSpace (L ⧸ H)] :
    IsClosed (L : Set A) := by
  let _ : LocallyCompactSpace L := locallyCompact_of_compact_kernel H hH
  exact closed_of_locallyCompact_subgroup L

lemma open_of_finiteIndex_compact_kernel_locallyCompact_quotient
    (L : Subgroup A) [L.FiniteIndex] (H : Subgroup L) [H.Normal]
    (hH : IsCompact (H : Set L)) [LocallyCompactSpace (L ⧸ H)] :
    IsOpen (L : Set A) :=
  L.isOpen_of_isClosed_of_finiteIndex
    (closed_of_compact_kernel_locallyCompact_quotient L H hH)

end CriticalPercolation.CompactQuotient
end
end

end OAI
