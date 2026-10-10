import Mathlib.Algebra.Group.Subgroup.Basic

namespace OAI

namespace GeneratedNormality

/-- A subgroup normalized by every member of a generating family is normal. -/
theorem normal_of_generating_family
    {K : Type*} [Group K] {ι : Sort*}
    (U : ι → Subgroup K) (hU : (⨆ i, U i) = ⊤)
    (Q : Subgroup K)
    (hn : ∀ i, U i ≤ Subgroup.normalizer (Q : Set K)) : Q.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  calc
    (⊤ : Subgroup K) = ⨆ i, U i := hU.symm
    _ ≤ Subgroup.normalizer (Q : Set K) := iSup_le hn

end GeneratedNormality

end OAI
