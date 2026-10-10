import OAI.NumberTheory.Ostmann.Construction.GraphCopySchedule

namespace OAI

/-! # The actual H/Y/pivot partition of the copied-slot schedule -/

namespace Ostmann

inductive CopyScheduleRole where
  | word
  | pivot (step : ℕ)
  | anchor (step : ℕ)
  | outside
  deriving DecidableEq

namespace CopyScheduleRole

def copiedAt (j : ℕ) : CopyScheduleRole → Bool
  | .word => true
  | .pivot k => decide (j < k)
  | .anchor k => decide (j = k)
  | .outside => false

def erasedAt (j : ℕ) : CopyScheduleRole → Bool
  | .pivot k => decide (j = k)
  | _ => false

def afterCopy (b : Bool) : CopyScheduleRole → CopyScheduleRole
  | .word => .word
  | .pivot k => if b then .pivot k else .outside
  | _ => .outside

end CopyScheduleRole

/-- The role of an actual copy, including the inactive negative pivot copies. -/
def copyScheduleRole {I : Type*} (role : I → CopyScheduleRole) :
    (n : ℕ) → CopyScheduleVertex I n → CopyScheduleRole
  | 0, i => role i
  | n + 1, .inl (b, i) => (copyScheduleRole role n i).afterCopy b
  | n + 1, .inr i => copyScheduleRole role n i

/-- Exactly the surviving labels. Copied labels come from H, retained labels
come from Y, and every constituent of the current pivot is removed. -/
def CopyScheduleSurvives {I : Type*} (role : I → CopyScheduleRole) :
    (n : ℕ) → CopyScheduleVertex I n → Prop
  | 0, _ => True
  | n + 1, .inl (_, i) => CopyScheduleSurvives role n i ∧
      (copyScheduleRole role n i).copiedAt n = true
  | n + 1, .inr i => CopyScheduleSurvives role n i ∧
      (copyScheduleRole role n i).copiedAt n = false ∧
      (copyScheduleRole role n i).erasedAt n = false

abbrev CopyScheduleH {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :=
  {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i ∧
    (copyScheduleRole role n i).copiedAt n = true}

abbrev CopyScheduleY {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :=
  {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i ∧
    (copyScheduleRole role n i).copiedAt n = false ∧
    (copyScheduleRole role n i).erasedAt n = false}

/-- This is a literal equivalence, not a count of an oversized ambient space. -/
def copyScheduleSurvivorEquiv {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    {i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i} ≃
      (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n where
  toFun i := match i with
    | ⟨.inl (b, j), h⟩ => .inl (b, ⟨j, h⟩)
    | ⟨.inr j, h⟩ => .inr ⟨j, h⟩
  invFun i := match i with
    | .inl (b, j) => ⟨.inl (b, j.val), j.property⟩
    | .inr j => ⟨.inr j.val, j.property⟩
  left_inv i := by
    rcases i with ⟨i, hi⟩
    cases i with
    | inl p => rcases p with ⟨b, j⟩; rfl
    | inr j => rfl
  right_inv i := by
    cases i with
    | inl p => rcases p with ⟨b, j⟩; rfl
    | inr j => rfl

theorem copyScheduleRole_path {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (t : Fin n → Bool) :
    copyScheduleRole role n (copySchedulePath n t i) = .word := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    change (copyScheduleRole role n (copySchedulePath n (fun k => t k.castSucc) i)).afterCopy _ = _
    rw [ih]
    rfl

theorem copyScheduleSurvives_path {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (t : Fin n → Bool) :
    CopyScheduleSurvives role n (copySchedulePath n t i) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    change CopyScheduleSurvives role n (copySchedulePath n (fun k => t k.castSucc) i) ∧ _
    exact ⟨ih _, by rw [copyScheduleRole_path role i hi]; rfl⟩

theorem copyScheduleRole_positive {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (k : ℕ) (hi : role i = .pivot k) (n : ℕ) :
    copyScheduleRole role n (copySchedulePositive n i) = .pivot k := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    change (copyScheduleRole role n (copySchedulePositive n i)).afterCopy true = _
    rw [ih]
    rfl

theorem copyScheduleSurvives_positive {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (k : ℕ) (hi : role i = .pivot k) (n : ℕ) (hn : n ≤ k) :
    CopyScheduleSurvives role n (copySchedulePositive n i) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    change CopyScheduleSurvives role n (copySchedulePositive n i) ∧ _
    refine ⟨ih (by omega), ?_⟩
    rw [copyScheduleRole_positive role i k hi]
    simpa [CopyScheduleRole.copiedAt] using (show n < k by omega)

@[simp] theorem copyScheduleRole_outside {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (i : I) : copyScheduleRole role n (copyScheduleOutside n i) = role i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- A reserved anchor really remains in Y until its designated step. -/
theorem copyScheduleSurvives_reserved {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (k : ℕ) (hi : role i = .anchor k) (n : ℕ) (hn : n ≤ k) :
    CopyScheduleSurvives role n (copyScheduleOutside n i) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    change CopyScheduleSurvives role n (copyScheduleOutside n i) ∧ _
    refine ⟨ih (by omega), ?_⟩
    rw [copyScheduleRole_outside, hi]
    simp [CopyScheduleRole.copiedAt, CopyScheduleRole.erasedAt, show n ≠ k by omega]

theorem copyScheduleRole_anchor {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (k : ℕ) (hi : role i = .anchor k) (n : ℕ) (hn : k < n) (b : Bool) :
    copyScheduleRole role n (copyScheduleAnchor n k b i) = .outside := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hk : k = n
    · subst k
      have he : copyScheduleAnchor (n + 1) n b i = .inl (b, copyScheduleOutside n i) := copyScheduleAnchor_new n b i
      rw [he]
      change (copyScheduleRole role n (copyScheduleOutside n i)).afterCopy b = _
      rw [copyScheduleRole_outside, hi]
      rfl
    · have he : copyScheduleAnchor (n + 1) k b i = .inr (copyScheduleAnchor n k b i) := copyScheduleAnchor_old n k b i hk
      rw [he]
      exact ih (by omega)

/-- Both fresh-anchor clones survive and thereafter remain outside. -/
theorem copyScheduleSurvives_anchor {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (k : ℕ) (hi : role i = .anchor k) (n : ℕ) (hn : k < n) (b : Bool) :
    CopyScheduleSurvives role n (copyScheduleAnchor n k b i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hk : k = n
    · subst k
      have he : copyScheduleAnchor (n + 1) n b i = .inl (b, copyScheduleOutside n i) := copyScheduleAnchor_new n b i
      rw [he]
      change CopyScheduleSurvives role n (copyScheduleOutside n i) ∧ _
      refine ⟨copyScheduleSurvives_reserved role i n hi n le_rfl, ?_⟩
      rw [copyScheduleRole_outside, hi]
      simp [CopyScheduleRole.copiedAt]
    · have he : copyScheduleAnchor (n + 1) k b i = .inr (copyScheduleAnchor n k b i) := copyScheduleAnchor_old n k b i hk
      rw [he]
      change CopyScheduleSurvives role n (copyScheduleAnchor n k b i) ∧ _
      refine ⟨ih (by omega), ?_⟩
      rw [copyScheduleRole_anchor role i k hi n (by omega)]
      exact ⟨rfl, rfl⟩

end Ostmann

end OAI
