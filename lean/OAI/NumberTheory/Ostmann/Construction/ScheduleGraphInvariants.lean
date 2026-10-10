import OAI.NumberTheory.Ostmann.Construction.CopyScheduleSupport
import OAI.NumberTheory.Ostmann.Construction.ScheduledAnchorGraph

namespace OAI

/-! # Regular rows and pivot columns on the surviving template slots -/

namespace Ostmann

/-- The row assertion is restricted to surviving slots, as required by the
actual H/Y partition; unused ambient labels are irrelevant. -/
def ScheduledRegularRow {I : Type*} (role : I → CopyScheduleRole)
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ)
    (i : CopyScheduleVertex I n) (ε : ℤ) : Prop :=
  ∀ j, CopyScheduleSurvives role n j → j ≠ i → copyScheduleGraph g pivot n i j = ε

theorem scheduledRegularRow_copy {I : Type*} (role : I → CopyScheduleRole)
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) (i : CopyScheduleVertex I n)
    (ε : ℤ) (hr : ScheduledRegularRow role g pivot n i ε)
    (hc : (copyScheduleRole role n i).copiedAt n = true)
    (hp : CopyScheduleSurvives role n (copySchedulePositive n (pivot n)))
    (hne : copySchedulePositive n (pivot n) ≠ i) (b : Bool) :
    ScheduledRegularRow role g pivot (n + 1) (.inl (b, i)) (transferCopySign b * ε) := by
  intro j hj hji
  cases j with
  | inl q =>
    rcases q with ⟨c, k⟩
    change CopyScheduleSurvives role n k ∧ _ at hj
    rw [copyScheduleGraph_copy_copy]
    by_cases hbc : b = c
    · subst c
      rw [ite_eq_left rfl, hr k hj.1]
      intro he
      subst k
      exact hji rfl
    · rw [ite_eq_right hbc, hr _ hp hne]
  | inr k =>
    change CopyScheduleSurvives role n k ∧ _ ∧ _ at hj
    rw [copyScheduleGraph_copy_outside, hr k hj.1]
    intro he
    subst k
    have : (true : Bool) = false := hc.symm.trans hj.2.1
    cases this

/-- Every copied word row has its accumulated sign, on the full current list. -/
theorem scheduledRegularRow_word {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (i : I) (hi : role i = .word) (n : ℕ) (t : Fin n → Bool) :
    ScheduledRegularRow role initialCompleteGraph pivot n (copySchedulePath n t i)
      (finalCopyParity t) := by
  induction n with
  | zero =>
    intro j _ hji
    exact initialCompleteGraph_of_ne hji.symm
  | succ n ih =>
    have hc : (copyScheduleRole role n (copySchedulePath n (fun k => t k.castSucc) i)).copiedAt n = true := by
      rw [copyScheduleRole_path role i hi]; rfl
    have hp := copyScheduleSurvives_positive role (pivot n) n (hpivot n) n le_rfl
    have hne : copySchedulePositive n (pivot n) ≠ copySchedulePath n (fun k => t k.castSucc) i := by
      intro he
      have h := congrArg (copyScheduleRole role n) he
      rw [copyScheduleRole_positive role (pivot n) n (hpivot n), copyScheduleRole_path role i hi] at h
      cases h
    have hr := scheduledRegularRow_copy role initialCompleteGraph pivot n _ _
      (ih (fun k => t k.castSucc)) hc hp hne (t (Fin.last n))
    have ht : Fin.snoc (fun k => t k.castSucc) (t (Fin.last n)) = t := Fin.snoc_init_self t
    rw [← ht, finalCopyParity_snoc, copySchedulePath_snoc]
    exact hr

/-- The unique active copy of a future pivot has regular row sign +1. -/
theorem scheduledRegularRow_pivot {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (i : I) (k : ℕ) (hi : role i = .pivot k) (n : ℕ) (hn : n ≤ k) :
    ScheduledRegularRow role initialCompleteGraph pivot n (copySchedulePositive n i) 1 := by
  induction n with
  | zero =>
    intro j _ hji
    exact initialCompleteGraph_of_ne hji.symm
  | succ n ih =>
    have hnk : n < k := by omega
    have hc : (copyScheduleRole role n (copySchedulePositive n i)).copiedAt n = true := by
      rw [copyScheduleRole_positive role i k hi]
      simpa [CopyScheduleRole.copiedAt] using hnk
    have hp := copyScheduleSurvives_positive role (pivot n) n (hpivot n) n le_rfl
    have hne : copySchedulePositive n (pivot n) ≠ copySchedulePositive n i := by
      intro he
      have h := congrArg (copyScheduleRole role n) he
      rw [copyScheduleRole_positive role (pivot n) n (hpivot n), copyScheduleRole_positive role i k hi] at h
      have : n = k := CopyScheduleRole.pivot.inj h
      omega
    have hr := scheduledRegularRow_copy role initialCompleteGraph pivot n _ _
      (ih (by omega)) hc hp hne true
    exact hr

/-- Every incoming row is constant on the constituents of a future pivot.
The targets are its actual positive copies, not a collapsed prime placeholder. -/
theorem copyScheduleGraph_pivot_common_column {I : Type*}
    (role : I → CopyScheduleRole) (pivot : ℕ → I)
    (k : ℕ) (a b : I) (ha : role a = .pivot k) (hb : role b = .pivot k)
    (n : ℕ) (hn : n ≤ k) (i : CopyScheduleVertex I n)
    (hi : CopyScheduleSurvives role n i) (hne : copyScheduleRole role n i ≠ .pivot k) :
    copyScheduleGraph initialCompleteGraph pivot n i (copySchedulePositive n a) =
      copyScheduleGraph initialCompleteGraph pivot n i (copySchedulePositive n b) := by
  induction n with
  | zero =>
    have hia : i ≠ a := fun he => hne (he ▸ ha)
    have hib : i ≠ b := fun he => hne (he ▸ hb)
    exact (initialCompleteGraph_of_ne hia).trans (initialCompleteGraph_of_ne hib).symm
  | succ n ih =>
    cases i with
    | inl p =>
      rcases p with ⟨c, i⟩
      change CopyScheduleSurvives role n i ∧ _ at hi
      cases c
      · rfl
      · change transferCopySign true * copyScheduleGraph initialCompleteGraph pivot n i
            (copySchedulePositive n a) =
          transferCopySign true * copyScheduleGraph initialCompleteGraph pivot n i
            (copySchedulePositive n b)
        apply congrArg (fun z => transferCopySign true * z)
        apply ih (by omega) i hi.1
        intro he
        apply hne
        change (copyScheduleRole role n i).afterCopy true = _
        rw [he]
        rfl
    | inr i =>
      change CopyScheduleSurvives role n i ∧ _ ∧ _ at hi
      change transferCopySign true * copyScheduleGraph initialCompleteGraph pivot n i
          (copySchedulePositive n a) =
        transferCopySign true * copyScheduleGraph initialCompleteGraph pivot n i
          (copySchedulePositive n b)
      exact congrArg (fun z => transferCopySign true * z) (ih (by omega) i hi.1 hne)

end Ostmann

end OAI
