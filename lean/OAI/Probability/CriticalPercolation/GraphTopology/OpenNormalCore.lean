import Mathlib

namespace OAI

section
noncomputable section
open Set Function Topology

namespace CriticalPercolation.CompactQuotient
variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]

lemma open_normalCore_of_finiteIndex_normalizer (J : Subgroup A)
    [(Subgroup.normalizer (J : Set A)).FiniteIndex] (hJ : IsOpen (J : Set A)) :
    IsOpen (J.normalCore : Set A) := by
  let r : A ⧸ (Subgroup.normalizer (J : Set A)) → A := Quotient.out
  have hr : ∀ q : A ⧸ (Subgroup.normalizer (J : Set A)), (r q : A ⧸ (Subgroup.normalizer (J : Set A)))=q := Quotient.out_eq'
  have he : (J.normalCore : Set A)=
      ⋂ q : A ⧸ (Subgroup.normalizer (J : Set A)), {x : A | (r q)⁻¹*x*r q∈J} := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_iInter,Set.mem_ofPred_eq]
      intro q
      simpa only [inv_inv] using hx (r q)⁻¹
    · intro hx g
      have hq : (r ((g⁻¹ : A) : A ⧸ (Subgroup.normalizer (J : Set A))))⁻¹*g⁻¹∈(Subgroup.normalizer (J : Set A)) :=
        (QuotientGroup.eq).mp (hr ((g⁻¹ : A) : A ⧸ (Subgroup.normalizer (J : Set A))))
      have hh := (Subgroup.mem_normalizer_iff''.mp hq ((r ((g⁻¹ : A) : A ⧸ (Subgroup.normalizer (J : Set A))))⁻¹*x*
        r ((g⁻¹ : A) : A ⧸ (Subgroup.normalizer (J : Set A))))).mp (Set.mem_iInter.mp hx ((g⁻¹ : A) : A ⧸ (Subgroup.normalizer (J : Set A))))
      simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left] using hh
  rw [he]
  exact isOpen_iInter_of_finite fun q => hJ.preimage
    ((continuous_const.mul continuous_id).mul continuous_const)

lemma compact_open_normalCore_of_finiteIndex_normalizer [T2Space A]
    (J : Subgroup A) [(Subgroup.normalizer (J : Set A)).FiniteIndex]
    (hc : IsCompact (J : Set A)) (ho : IsOpen (J : Set A)) :
    IsCompact (J.normalCore : Set A) ∧ IsOpen (J.normalCore : Set A) :=
  ⟨hc.of_isClosed_subset (J.normalCore_isClosed hc.isClosed) J.normalCore_le,
    open_normalCore_of_finiteIndex_normalizer J ho⟩

end CriticalPercolation.CompactQuotient
end
end

end OAI
