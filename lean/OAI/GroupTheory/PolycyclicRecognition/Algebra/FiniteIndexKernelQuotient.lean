import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteTorsionPowerSubgroup
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OAI

/-! # Quotienting by a characteristic finite-index subgroup of the kernel -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]
  (K : Subgroup N) [K.Characteristic]

def finiteIndexKernelQuotientMap : G ⧸ K.map N.subtype →* G ⧸ N :=
  QuotientGroup.map (K.map N.subtype) N (MonoidHom.id G) (by
    rintro _ ⟨n, _, rfl⟩
    exact n.property)

theorem finiteIndexKernelQuotientMap_surjective :
    Function.Surjective (finiteIndexKernelQuotientMap N K) := by
  apply QuotientGroup.map_surjective_of_surjective
  exact QuotientGroup.mk'_surjective N

theorem finiteIndexKernelQuotientMap_kernel_finite [K.FiniteIndex] :
    Finite (finiteIndexKernelQuotientMap N K).ker := by
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
  let : ψ.ker.FiniteIndex := hψ.symm ▸ (inferInstance : K.FiniteIndex)
  let : Finite ψ.range := Finite.of_equiv (N ⧸ ψ.ker)
    (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  have hk : (finiteIndexKernelQuotientMap N K).ker = N.map π := by
    simp only [finiteIndexKernelQuotientMap, QuotientGroup.ker_map, Subgroup.comap_id]
    rfl
  have he : N.map π = ψ.range := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, n.property, rfl⟩
  exact (hk.trans he).symm ▸ (inferInstance : Finite ψ.range)

end PolycyclicRecognition

end

end OAI
