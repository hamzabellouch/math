import OAI.Combinatorics.ContingencyTables.Sampling.SmallRepairWords

namespace OAI

/-! # The defect coordinates are determined by the two integer views -/

namespace ContingencyTables

variable {I J : Type*} [DecidableEq I] [DecidableEq J]

theorem IsDefect.labels_unique {x q : I → J → ℕ} {s t s' t' : I×J}
    (h : IsDefect x q s t) (h' : IsDefect x q s' t') : s=s' ∧ t=t' := by
  have hst : ¬(s.1=t.1 ∧ s.2=t.2) := fun he => h.1 (Prod.ext he.1 he.2)
  have hs := h.2 s.1 s.2
  simp only [transferInt,hst,ite_false,and_self,ite_true,sub_zero] at hs
  have hss : s=s' := by
    by_contra he
    have hss' : ¬(s.1=s'.1 ∧ s.2=s'.2) := fun hh => he (Prod.ext hh.1 hh.2)
    have hs' := h'.2 s.1 s.2
    simp only [transferInt,hss',ite_false,add_zero] at hs'
    split_ifs at hs' <;> omega
  subst s'
  refine ⟨rfl,?_⟩
  by_contra he
  have htt : ¬(t.1=t'.1 ∧ t.2=t'.2) := fun hh => he (Prod.ext hh.1 hh.2)
  have hts : ¬(t.1=s.1 ∧ t.2=s.2) := fun hh => h.1 (Prod.ext hh.1.symm hh.2.symm)
  have ht := h.2 t.1 t.2
  have ht' := h'.2 t.1 t.2
  simp only [transferInt,htt,hts,ite_false,and_self,ite_true,sub_zero,add_zero] at ht ht'
  omega

namespace SmallGraphProfiles
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma defectLabels_eq_of_spec (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : PositiveDefects small B r c L)
    (st : Cells small×Cells small)
    (h : IsDefect (smallView small (naturalProfile z.val) false)
      (smallQ small B (naturalProfile z.val)) st.1.val st.2.val) :
    defectLabels small B r c L z=st := by
  have he := (defectLabels_spec small B r c L z).labels_unique h
  exact Prod.ext (Subtype.ext he.1) (Subtype.ext he.2)

end SmallGraphProfiles
end ContingencyTables

end OAI
