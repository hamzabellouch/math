import OAI.NumberTheory.Ostmann.Construction.ScheduledPrimePhase

namespace OAI

/-! # Forgetting constituent indices commutes with the literal copy schedule -/

namespace Ostmann

/-- Apply a map of original labels without changing any copy/retain choice. -/
def copyScheduleMap {I J : Type*} (f : I → J) :
    (n : ℕ) → CopyScheduleVertex I n → CopyScheduleVertex J n
  | 0, i => f i
  | n + 1, .inl (b, i) => .inl (b, copyScheduleMap f n i)
  | n + 1, .inr i => .inr (copyScheduleMap f n i)

@[simp] theorem copyScheduleOrigin_map {I J : Type*} (f : I → J)
    (n : ℕ) (i : CopyScheduleVertex I n) :
    copyScheduleOrigin n (copyScheduleMap f n i) = f (copyScheduleOrigin n i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases i with ⟨b, i⟩ | i <;> exact ih i

@[simp] theorem copyScheduleMap_positive {I J : Type*} (f : I → J) (n : ℕ) (i : I) :
    copyScheduleMap f n (copySchedulePositive n i) = copySchedulePositive n (f i) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun i => Sum.inl (true, i)) ih

@[simp] theorem copyScheduleMap_path {I J : Type*} (f : I → J) (n : ℕ)
    (path : Fin n → Bool) (i : I) :
    copyScheduleMap f n (copySchedulePath n path i) = copySchedulePath n path (f i) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun i => Sum.inl (path (Fin.last n), i)) (ih _)

@[simp] theorem copyScheduleRole_map {I J : Type*} (f : I → J)
    (role : J → CopyScheduleRole) (n : ℕ) (i : CopyScheduleVertex I n) :
    copyScheduleRole role n (copyScheduleMap f n i) = copyScheduleRole (role ∘ f) n i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases i with ⟨b, i⟩ | i
    · exact congrArg (fun r => r.afterCopy b) (ih i)
    · exact ih i

/-- The prime constituents of an atom survive precisely when the atom does. -/
theorem copyScheduleSurvives_map_iff {I J : Type*} (f : I → J)
    (role : J → CopyScheduleRole) (n : ℕ) (i : CopyScheduleVertex I n) :
    CopyScheduleSurvives role n (copyScheduleMap f n i) ↔
      CopyScheduleSurvives (role ∘ f) n i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases i with ⟨b, i⟩ | i
    · change (_ ∧ _) ↔ (_ ∧ _)
      rw [ih, copyScheduleRole_map]
    · change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
      rw [ih, copyScheduleRole_map]

end Ostmann

end OAI
