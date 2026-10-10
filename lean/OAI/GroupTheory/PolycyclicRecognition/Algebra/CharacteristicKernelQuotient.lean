import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteIndexKernelQuotient

namespace OAI

/-! # The kernel after quotienting by a characteristic subgroup

The comparison does not require the characteristic subgroup to have finite
index. In particular it applies to the full nilpotent torsion subgroup.
-/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]
  (K : Subgroup N) [K.Characteristic]

def characteristicKernelQuotientEquiv :
    (N ⧸ K) ≃* (finiteIndexKernelQuotientMap N K).ker := by
  let A := K.map N.subtype
  let π := QuotientGroup.mk' A
  let ψ : N →* G ⧸ A := π.comp N.subtype
  have hψ : ψ.ker = K := by
    ext n
    change (↑(n : G) : G ⧸ A) = 1 ↔ n ∈ K
    rw [QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨a, ha, han⟩
      exact (Subtype.ext han : a = n) ▸ ha
    · intro hn
      exact ⟨n, hn, rfl⟩
  have hk : (finiteIndexKernelQuotientMap N K).ker = ψ.range := by
    have hr : N.map π = ψ.range := by
      ext x
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨n, hn⟩, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨n, n.property, rfl⟩
    rw [← hr]
    simp only [finiteIndexKernelQuotientMap, QuotientGroup.ker_map, Subgroup.comap_id]
    rfl
  exact (QuotientGroup.quotientMulEquivOfEq hψ.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hk.symm))

end PolycyclicRecognition

end

end OAI
