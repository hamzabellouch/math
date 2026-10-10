import Mathlib.Data.List.FinRange
import OAI.NumberTheory.Ostmann.Construction.ConstituentScheduleEquiv
import OAI.NumberTheory.Ostmann.Construction.ExpandedScheduledTemplate

namespace OAI

/-! # The exact constituent words of the surviving grouped atoms -/

namespace Ostmann

open scoped BigOperators Classical

abbrev SurvivingConstituent {I : Type*} (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) :=
  {v : CopyScheduleVertex (Σ i, Fin (size i)) n // CopyScheduleSurvives (role ∘ Sigma.fst) n v}

noncomputable def scheduleConstituentWord {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n) :
    List (SurvivingConstituent role size n) :=
  List.ofFn (fun k : Fin (size (copyScheduleOrigin n v.val)) =>
    (survivingConstituentEquiv role size n).symm ⟨v, k⟩)

theorem scheduleConstituentWord_length {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n) :
    (scheduleConstituentWord role size n v).length = size (copyScheduleOrigin n v.val) := by
  exact List.length_ofFn

theorem scheduleConstituentWord_nodup {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n) :
    (scheduleConstituentWord role size n v).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro k l he
  have h := (survivingConstituentEquiv role size n).symm.injective he
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

theorem scheduleConstituentWord_disjoint {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v w : CopyScheduleAtoms role n) (hvw : v ≠ w) :
    List.Disjoint (scheduleConstituentWord role size n v) (scheduleConstituentWord role size n w) := by
  intro i hi hj
  obtain ⟨k, hk⟩ := List.mem_ofFn.mp hi
  obtain ⟨l, hl⟩ := List.mem_ofFn.mp hj
  apply hvw
  exact congrArg Sigma.fst ((survivingConstituentEquiv role size n).symm.injective (hk.trans hl.symm))

theorem scheduleConstituentWord_prod {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n)
    (q : SurvivingConstituent role size n → ℕ) :
    ((scheduleConstituentWord role size n v).map q).prod =
      ∏ k : Fin (size (copyScheduleOrigin n v.val)), q ((survivingConstituentEquiv role size n).symm ⟨v, k⟩) := by
  rw [scheduleConstituentWord, List.map_ofFn, List.prod_ofFn]
  rfl

/-- Multiplying all grouped words gives the original total prime product,
without omission or repeated use of a constituent. -/
theorem scheduleConstituentWord_total_prod {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (q : SurvivingConstituent role size n → ℕ) :
    (∏ v : CopyScheduleAtoms role n, ((scheduleConstituentWord role size n v).map q).prod) = ∏ i, q i := by
  simp only [scheduleConstituentWord_prod]
  rw [← Fintype.prod_sigma (fun z => q ((survivingConstituentEquiv role size n).symm z))]
  exact (survivingConstituentEquiv role size n).symm.prod_comp q

/-- Constituent-level pairwise coprimality implies the exact top grouped
coprimality required by the full Fourier coefficient. -/
theorem scheduleConstituentWord_pairwise {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (q : SurvivingConstituent role size n → ℕ)
    (hq : Pairwise (fun i j => (q i).Coprime (q j))) :
    Pairwise (fun v w : CopyScheduleAtoms role n =>
      ((scheduleConstituentWord role size n v).map q).prod.Coprime
        ((scheduleConstituentWord role size n w).map q).prod) := by
  intro v w hvw
  rw [scheduleConstituentWord_prod, scheduleConstituentWord_prod]
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro l
  apply hq
  intro he
  apply hvw
  exact congrArg Sigma.fst ((survivingConstituentEquiv role size n).symm.injective he)

end Ostmann

end OAI
