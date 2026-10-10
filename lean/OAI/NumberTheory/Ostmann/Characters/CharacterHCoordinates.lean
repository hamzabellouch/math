import OAI.NumberTheory.Ostmann.Characters.CharacterScheduleRoles
import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalPrimeRanges

namespace OAI

/-! # Exact whole-atom coordinates of the character argument's copied block -/
namespace Ostmann
open scoped Classical BigOperators

theorem surviving_anchor_is_reserved {I : Type*} (role : I → CopyScheduleRole)
    (n k : ℕ) (v : CopyScheduleVertex I n)
    (hv : CopyScheduleSurvives role n v) (ha : copyScheduleRole role n v = .anchor k) :
    n ≤ k ∧ ∃ i, role i = .anchor k ∧ v = copyScheduleOutside n i := by
  induction n with
  | zero => exact ⟨Nat.zero_le _, v, ha, rfl⟩
  | succ n ih =>
    cases v with
    | inl q =>
      rcases q with ⟨b, v⟩
      change (copyScheduleRole role n v).afterCopy b = .anchor k at ha
      cases h : copyScheduleRole role n v <;> cases b <;>
        simp [h, CopyScheduleRole.afterCopy] at ha
    | inr v =>
      change copyScheduleRole role n v = .anchor k at ha
      obtain ⟨hn, i, hi, he⟩ := ih v hv.1 ha
      have hne : n ≠ k := by
        have hh := hv.2.1
        change (copyScheduleRole role n v).copiedAt n = false at hh
        rw [ha] at hh
        change decide (n = k) = false at hh
        exact of_decide_eq_false hh
      exact ⟨by omega, i, hi, congrArg Sum.inr he⟩

theorem characterRole_word_unique {k : ℕ} (i : CharacterRole k)
    (hi : characterRole k i = .word) : i = (true, none) := by
  rcases i with ⟨b, c⟩
  cases b with
  | false => simp [characterRole, signedAtomRole] at hi
  | true =>
    cases c with
    | none => rfl
    | some c =>
      rcases c with j | ⟨j, b⟩ | u <;>
        simp [characterRole, signedAtomRole, characterPositiveRole] at hi

theorem characterRole_pivot_exists {k j : ℕ} (i : CharacterRole k)
    (hi : characterRole k i = .pivot j) : ∃ t : Fin k, t.val = j ∧ i = characterPivotAtom t := by
  rcases i with ⟨b, c⟩
  cases b with
  | false => simp [characterRole, signedAtomRole] at hi
  | true =>
    cases c with
    | none => simp [characterRole, signedAtomRole, characterPositiveRole] at hi
    | some c =>
      rcases c with t | ⟨t, b⟩ | u
      · exact ⟨t, CopyScheduleRole.pivot.inj hi, rfl⟩
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hi
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hi

theorem characterRole_anchor_exists {k j : ℕ} (i : CharacterRole k)
    (hi : characterRole k i = .anchor j) :
    ∃ t : Fin k, ∃ b : Bool, t.val = j ∧ i = characterAnchorAtom t b := by
  rcases i with ⟨b, c⟩
  cases b with
  | false => simp [characterRole, signedAtomRole] at hi
  | true =>
    cases c with
    | none => simp [characterRole, signedAtomRole, characterPositiveRole] at hi
    | some c =>
      rcases c with t | ⟨t, b⟩ | u
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hi
      · exact ⟨t, b, CopyScheduleRole.anchor.inj hi, rfl⟩
      · simp [characterRole, signedAtomRole, characterPositiveRole] at hi

abbrev CharacterHIndex (k n : ℕ) := (Fin n → Bool) ⊕ ({j : Fin k // n < j.val} ⊕ Bool)

noncomputable def characterHCoordinate {k n : ℕ} (hn : n < k) :
    CharacterHIndex k n → CopyScheduleH (characterRole k) n
  | .inl t => scheduledWordH (characterRole k) n t ⟨(true, none), rfl⟩
  | .inr (.inl j) => ⟨copySchedulePositive n (characterPivotAtom j.val),
      copyScheduleSurvives_positive _ _ j.val.val (characterRole_pivot _) n j.property.le,
      by rw [copyScheduleRole_positive _ _ j.val.val (characterRole_pivot _)];
         simpa only [CopyScheduleRole.copiedAt, decide_eq_true_eq] using j.property⟩
  | .inr (.inr b) => ⟨copyScheduleOutside n (characterAnchorAtom ⟨n, hn⟩ b),
      copyScheduleSurvives_reserved _ _ n (characterRole_anchor _ _) n le_rfl,
      by rw [copyScheduleRole_outside, characterRole_anchor];
         simp only [CopyScheduleRole.copiedAt, decide_true]⟩

@[simp] theorem characterHCoordinate_role {k n : ℕ} (hn : n < k) (x : CharacterHIndex k n) :
    copyScheduleRole (characterRole k) n (characterHCoordinate hn x).val =
      match x with
      | .inl _ => .word
      | .inr (.inl j) => .pivot j.val.val
      | .inr (.inr _) => .anchor n := by
  rcases x with t | (j | b)
  · exact copyScheduleRole_path _ _ rfl n t
  · exact copyScheduleRole_positive _ _ j.val.val (characterRole_pivot _) n
  · exact copyScheduleRole_outside _ n _

@[simp] theorem characterHCoordinate_origin {k n : ℕ} (hn : n < k) (x : CharacterHIndex k n) :
    copyScheduleOrigin n (characterHCoordinate hn x).val =
      match x with
      | .inl _ => (true, none)
      | .inr (.inl j) => characterPivotAtom j.val
      | .inr (.inr b) => characterAnchorAtom ⟨n, hn⟩ b := by
  rcases x with t | (j | b)
  · exact copyScheduleOrigin_path n t _
  · exact copyScheduleOrigin_positive n _
  · exact copyScheduleOrigin_outside n _

theorem characterHCoordinate_injective {k n : ℕ} (hn : n < k) :
    Function.Injective (characterHCoordinate hn) := by
  intro x y h
  have hr := congrArg (fun h : CopyScheduleH (characterRole k) n =>
    copyScheduleRole (characterRole k) n h.val) h
  simp only [characterHCoordinate_role] at hr
  rcases x with t | (j | b) <;> rcases y with u | (l | c)
  · have ht := @copySchedulePath_injective (CharacterRole k) n (t, (true, none))
      (u, (true, none)) (congrArg Subtype.val h)
    exact congrArg Sum.inl (congrArg Prod.fst ht)
  · cases hr
  · cases hr
  · cases hr
  · have he : j = l := Subtype.ext (Fin.ext (CopyScheduleRole.pivot.inj hr))
    exact congrArg (fun j => Sum.inr (Sum.inl j)) he
  · cases hr
  · cases hr
  · cases hr
  · have ho := congrArg (fun h : CopyScheduleH (characterRole k) n =>
      copyScheduleOrigin n h.val) h
    simp only [characterHCoordinate_origin, characterAnchorAtom, Prod.mk.injEq,
      Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq, true_and] at ho
    exact congrArg (fun b => Sum.inr (Sum.inr b)) ho

theorem characterHCoordinate_surjective {k n : ℕ} (hn : n < k) :
    Function.Surjective (characterHCoordinate hn) := by
  intro h
  cases hr : copyScheduleRole (characterRole k) n h.val with
  | word =>
    obtain ⟨t, i, hi, he⟩ := surviving_word_is_path _ n h.val h.property.1 hr
    have hi' := characterRole_word_unique i hi
    subst i
    exact ⟨.inl t, Subtype.ext he.symm⟩
  | pivot j =>
    obtain ⟨_, i, hi, he⟩ := surviving_pivot_is_positive _ n j h.val h.property.1 hr
    obtain ⟨t, ht, rfl⟩ := characterRole_pivot_exists i hi
    have hnj : n < j := by
      have hh := h.property.2
      rw [hr] at hh
      simpa only [CopyScheduleRole.copiedAt, decide_eq_true_eq] using hh
    refine ⟨.inr (.inl ⟨t, by omega⟩), Subtype.ext he.symm⟩
  | anchor j =>
    obtain ⟨_, i, hi, he⟩ := surviving_anchor_is_reserved _ n j h.val h.property.1 hr
    obtain ⟨t, b, ht, rfl⟩ := characterRole_anchor_exists i hi
    have hnj : n = j := by
      have hh := h.property.2
      rw [hr] at hh
      simpa only [CopyScheduleRole.copiedAt, decide_eq_true_eq] using hh
    have ht' : t = ⟨n, hn⟩ := Fin.ext (ht.trans hnj.symm)
    subst t
    exact ⟨.inr (.inr b), Subtype.ext he.symm⟩
  | outside =>
    have hh := h.property.2
    rw [hr] at hh
    cases hh

noncomputable def characterHEquiv {k n : ℕ} (hn : n < k) :
    CharacterHIndex k n ≃ CopyScheduleH (characterRole k) n :=
  Equiv.ofBijective (characterHCoordinate hn)
    ⟨characterHCoordinate_injective hn, characterHCoordinate_surjective hn⟩

/-- Exactly the full words, future pivot groups, and the two fresh anchors
occur in H. Inactive copies make no contribution. -/
theorem character_H_product {k n : ℕ} (hn : n < k) {M : Type*} [CommMonoid M]
    (w : CharacterRole k → M) :
    (∏ h : CopyScheduleH (characterRole k) n, w (copyScheduleOrigin n h.val)) =
      w (true, none) ^ (2 ^ n) *
        ((∏ j : {j : Fin k // n < j.val}, w (characterPivotAtom j.val)) *
          ∏ b : Bool, w (characterAnchorAtom ⟨n, hn⟩ b)) := by
  rw [← (characterHEquiv hn).prod_comp]
  change (∏ x : CharacterHIndex k n,
    w (copyScheduleOrigin n (characterHCoordinate hn x).val)) = _
  simp only [characterHCoordinate_origin, Fintype.prod_sum_type, Finset.prod_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

end Ostmann

end OAI
