import OAI.Analysis.CircleDomains.Sobolev.PartitionMixing
import Mathlib.Topology.Compactness.LocallyFinite

namespace OAI

/-! Only finitely many members of a locally finite open-domain partition
meet a compactly supported test. Their products sum exactly to the test. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace OpenPlanePartition

 theorem finite_test_decomposition {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) {φ : EuclideanPlane → ℝ}
    (hs : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω) :
    ∃ F : Finset ι, φ = fun x => ∑ j ∈ F, ρ.weight j x*φ x := by
  classical
  have hK : IsCompact ((Subtype.val : Ω → EuclideanPlane) ⁻¹' tsupport φ) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hs (by simpa only [Subtype.range_coe] using hsub)
  have hfin := ρ.locallyFinite.finite_nonempty_inter_compact hK
  refine ⟨hfin.toFinset,?_⟩
  funext x
  by_cases hx : φ x = 0
  · simp only [hx,mul_zero,Finset.sum_const_zero]
  · have hxK : x ∈ tsupport φ := subset_tsupport φ hx
    have hxΩ : x ∈ Ω := hsub hxK
    have hin : support (fun j => ρ.weight j x) ⊆ hfin.toFinset := by
      intro j hj
      apply hfin.mem_toFinset.mpr
      exact ⟨⟨x,hxΩ⟩,hj,hxK⟩
    have hw : (∑ᶠ j, ρ.weight j x) = ∑ j ∈ hfin.toFinset, ρ.weight j x :=
      finsum_eq_sum_of_support_subset _ hin
    rw [← Finset.sum_mul,← hw,ρ.sum_one ⟨x,hxΩ⟩,one_mul]

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
