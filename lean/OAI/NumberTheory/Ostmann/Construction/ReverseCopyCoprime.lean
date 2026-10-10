import OAI.NumberTheory.Ostmann.Construction.ScheduleInheritedCoprime

namespace OAI

/-! # Pairwise coprimality survives a reverse copy step -/

namespace Ostmann

open scoped Classical

theorem CopyScheduleRole.erasedAt_eq_true_iff (r : CopyScheduleRole) (n : ℕ) :
    r.erasedAt n = true ↔ r = .pivot n := by
  cases r <;> simp [erasedAt, eq_comm]

theorem erased_schedule_atoms_unique {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (hu : ∀ a b, role a = .pivot n → role b = .pivot n → a = b)
    (i j : CopyScheduleAtoms role n)
    (hi : (copyScheduleRole role n i.val).erasedAt n = true)
    (hj : (copyScheduleRole role n j.val).erasedAt n = true) : i = j := by
  obtain ⟨_, a, ha, hea⟩ := surviving_pivot_is_positive role n n i.val i.property
    ((CopyScheduleRole.erasedAt_eq_true_iff _ _).mp hi)
  obtain ⟨_, b, hb, heb⟩ := surviving_pivot_is_positive role n n j.val j.property
    ((CopyScheduleRole.erasedAt_eq_true_iff _ _).mp hj)
  apply Subtype.ext
  rw [hea, heb, hu a b ha hb]

theorem reverseCopyLabelMap_pairwise_coprime {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (P : ℕ) (x : CopyScheduleAtoms role (n + 1) → ℕ)
    (hu : ∀ a c, role a = .pivot n → role c = .pivot n → a = c)
    (hpair : Pairwise (fun i j => (x i).Coprime (x j)))
    (hP : ∀ i, P.Coprime (x i)) :
    Pairwise (fun i j => (reverseCopyLabelMap role n b P x i).Coprime
      (reverseCopyLabelMap role n b P x j)) := by
  intro i j hij
  unfold reverseCopyLabelMap
  split_ifs with hic hjc hje hie hjc hje hjc hje
  · apply hpair
    intro he
    apply hij
    apply Subtype.ext
    exact (Prod.mk.inj (Sum.inl.inj (congrArg Subtype.val he))).2
  · exact (hP _).symm
  · apply hpair
    intro he
    have hv := congrArg Subtype.val he
    cases hv
  · exact hP _
  · exact False.elim (hij (erased_schedule_atoms_unique role n hu i j hie hje))
  · exact hP _
  · apply hpair
    intro he
    have hv := congrArg Subtype.val he
    cases hv
  · exact (hP _).symm
  · apply hpair
    intro he
    apply hij
    exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val he))

end Ostmann

end OAI
