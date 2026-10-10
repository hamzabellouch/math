import OAI.NumberTheory.Ostmann.Construction.InitialScheduleWordAmplitude
import OAI.NumberTheory.Ostmann.Arithmetic.FiniteArithmeticIteration

namespace OAI

/-! # The finite role set used in the nonquadratic character argument

A positive word, finitely many pivot groups, two fresh anchors at each step,
and one filler have independent negative copies. Only the positive word,
pivots and anchors participate in the copy schedule.
-/
namespace Ostmann
open scoped Classical BigOperators

abbrev CharacterCell (k : ℕ) := Fin k ⊕ ((Fin k × Bool) ⊕ Unit)
abbrev CharacterRole (k : ℕ) := Bool × Option (CharacterCell k)

def characterPositiveRole (k : ℕ) : Option (CharacterCell k) → CopyScheduleRole
  | none => .word
  | some (.inl j) => .pivot j.val
  | some (.inr (.inl (j, _))) => .anchor j.val
  | some (.inr (.inr _)) => .outside

def characterRole (k : ℕ) : CharacterRole k → CopyScheduleRole :=
  signedAtomRole (characterPositiveRole k)

def characterCellSize {k : ℕ} (r : Fin k → ℕ) (f : ℕ) : CharacterCell k → ℕ
  | .inl j => r j
  | .inr (.inl _) => 1
  | .inr (.inr _) => f

def characterSize {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) : CharacterRole k → ℕ :=
  fun v => initialWordSize (m + 1) (characterCellSize r f) v.2

def characterPivotAtom {k : ℕ} (j : Fin k) : CharacterRole k :=
  (true, some (.inl j))

def characterAnchorAtom {k : ℕ} (j : Fin k) (b : Bool) : CharacterRole k :=
  (true, some (.inr (.inl (j, b))))

@[simp] theorem characterRole_word (k : ℕ) : characterRole k (true, none) = .word := rfl
@[simp] theorem characterRole_pivot {k : ℕ} (j : Fin k) :
    characterRole k (characterPivotAtom j) = .pivot j.val := rfl
@[simp] theorem characterRole_anchor {k : ℕ} (j : Fin k) (b : Bool) :
    characterRole k (characterAnchorAtom j b) = .anchor j.val := rfl

@[simp] theorem characterSize_word {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    characterSize m r f (true, none) = m + 1 := rfl
@[simp] theorem characterSize_pivot {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) (j : Fin k) :
    characterSize m r f (characterPivotAtom j) = r j := rfl
@[simp] theorem characterSize_anchor {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (j : Fin k) (b : Bool) : characterSize m r f (characterAnchorAtom j b) = 1 := rfl

/-- The actual positive word, including its one top label. -/
noncomputable def characterWordEquiv {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    Fin (m + 1) ≃ {i : Σ v, Fin (characterSize m r f v) // characterRole k i.1 = .word} :=
  Equiv.ofBijective (fun t => ⟨⟨(true, none), t⟩, rfl⟩) (by
    constructor
    · intro a b h
      have hs : (⟨(true, none), a⟩ : Σ v, Fin (characterSize m r f v)) = ⟨(true, none), b⟩ :=
        congrArg Subtype.val h
      cases hs
      rfl
    · rintro ⟨⟨⟨b, c⟩, t⟩, ht⟩
      cases b with
      | false => simp [characterRole, signedAtomRole] at ht
      | true =>
        cases c with
        | none => exact ⟨t, rfl⟩
        | some c =>
          rcases c with j | a | u <;>
            simp [characterRole, signedAtomRole, characterPositiveRole] at ht)

theorem characterPivotAtom_unique {k : ℕ} (j : Fin k) (v : CharacterRole k)
    (hv : characterRole k v = .pivot j.val) : v = characterPivotAtom j := by
  rcases v with ⟨b, c⟩
  cases b with
  | false => simp [characterRole, signedAtomRole] at hv
  | true =>
    cases c with
    | none => simp [characterRole, signedAtomRole, characterPositiveRole] at hv
    | some c =>
      rcases c with i | a | u
      · have hi : i = j := Fin.ext (CopyScheduleRole.pivot.inj hv)
        subst i
        rfl
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hv
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hv

/-- Extend the finitely many real pivots by an arbitrary existing word slot.
All transfer theorems use only the genuine prefix. -/
noncomputable def characterPivot {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (hr : ∀ j, 0 < r j) (j : ℕ) : Σ v, Fin (characterSize m r f v) :=
  if h : j < k then ⟨characterPivotAtom ⟨j, h⟩, ⟨0, hr ⟨j, h⟩⟩⟩
  else ⟨(true, none), ⟨0, Nat.succ_pos m⟩⟩

@[simp] theorem characterPivot_role {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (hr : ∀ j, 0 < r j) (j : ℕ) (hj : j < k) :
    characterRole k (characterPivot m r f hr j).1 = .pivot j := by
  simp [characterPivot, hj]

def characterAnchor {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (j : Fin k) (b : Bool) : Σ v, Fin (characterSize m r f v) :=
  ⟨characterAnchorAtom j b, ⟨0, Nat.zero_lt_one⟩⟩

@[simp] theorem characterAnchor_role {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (j : Fin k) (b : Bool) : characterRole k (characterAnchor m r f j b).1 = .anchor j.val := rfl

theorem characterAnchor_ne {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) (j : Fin k) :
    characterAnchor m r f j false ≠ characterAnchor m r f j true := by
  intro h
  have he := congrArg (fun i => i.1) h
  simp only [characterAnchor, characterAnchorAtom, Prod.mk.injEq, Option.some.injEq,
    Sum.inr.injEq, Sum.inl.injEq, true_and] at he
  exact Bool.false_ne_true he

/-- Every retained H permutation preserves the original signed character. -/
theorem characterSchedule_matching {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH
      (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1) n))
    (h : CopyScheduleH
      (fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1) n) :
    signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
        (copyScheduleOrigin n (e h).val) =
      signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
        (copyScheduleOrigin n h.val) :=
  signedAtomCharacter_matching (characterPositiveRole k)
    (initialWordSize (m + 1) (characterCellSize r f)) χ n e h

end Ostmann

end OAI
