import OAI.Combinatorics.ContingencyTables.Rooted.LargePairEnumeration

namespace OAI

/-! # Removing the arbitrary enumeration from the physical large-cell sum -/

namespace ContingencyTables.PhysicalLargeProfiles

open scoped BigOperators Classical
open LargePairEnumeration

variable {C : Type*}

@[reducible] def PhysicalAssignments (small : C → Bool) (M : C → ℕ) :=
  (l : LargeCell small) → Fin (M l.val+1)

noncomputable def physicalProfile (small : C → Bool) (M : C → ℕ)
    (z : SmallView small → ℕ) (a : PhysicalAssignments small M) (u : C×Bool) : ℕ :=
  if hs : small u.1=true then z (⟨u.1,hs⟩,u.2)
  else if u.2 then M u.1-(a ⟨u.1,Bool.eq_false_iff.mpr hs⟩).val
    else (a ⟨u.1,Bool.eq_false_iff.mpr hs⟩).val

lemma joinedProfile_physical {n : ℕ} (small : C → Bool) (M : C → ℕ)
    (e : Fin n ≃ LargeCell small) (z : SmallView small → ℕ)
    (a : PhysicalAssignments small M) :
    joinedProfile (fun k => M (e k).val) z
      ((Equiv.piCongrLeft (fun l : LargeCell small => Fin (M l.val+1)) e).symm a) ∘
      (physicalJoinEquiv small e).symm=physicalProfile small M z a := by
  funext u
  rcases u with ⟨c,b⟩
  by_cases hs : small c=true
  · simp [physicalJoinEquiv,partitionEquiv,joinedProfile,physicalProfile,hs]
  · simp [physicalJoinEquiv,partitionEquiv,joinedProfile,physicalProfile,hs]
    have hval := congrArg (fun l : LargeCell small => (a l).val)
      (e.apply_symm_apply ⟨c,Bool.eq_false_iff.mpr hs⟩)
    exact congrArg (fun t : ℕ => if b then M c-t else t) hval

variable [Fintype C]

/-- The physical finite sum is independent of the order used to enumerate
large cells in the recursive signature proof. -/
theorem sum_joined_eq_physical {n : ℕ} (small : C → Bool) (M : C → ℕ)
    (e : Fin n ≃ LargeCell small) (z : SmallView small → ℕ)
    (F : (C×Bool → ℕ) → ℝ) :
    (∑ a : ((k : Fin n) → Fin (M (e k).val+1)),
      F (joinedProfile (fun k => M (e k).val) z a ∘ (physicalJoinEquiv small e).symm))=
      ∑ a : PhysicalAssignments small M, F (physicalProfile small M z a) := by
  apply Fintype.sum_equiv (Equiv.piCongrLeft (fun l : LargeCell small => Fin (M l.val+1)) e)
  intro a
  congr 1
  have h := joinedProfile_physical small M e z
    ((Equiv.piCongrLeft (fun l : LargeCell small => Fin (M l.val+1)) e) a)
  simpa only [Equiv.symm_apply_apply] using h

end ContingencyTables.PhysicalLargeProfiles

end OAI
