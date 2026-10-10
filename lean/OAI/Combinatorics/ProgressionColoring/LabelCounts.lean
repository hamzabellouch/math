import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

universe uU uV uAlpha uWord

namespace QuantitativeVanDerWaerden

open scoped BigOperators

/-- A full label retains the literal first and second interval labels. -/
abbrev FullLabel (D : ℕ) (U : Type uU) (V : Type uV) := (Fin D → U) × (Fin D → V)

/-- The full output is dummy exactly when some second-coordinate output is
dummy. Stationary coordinates are supplied as `some` of their untruncated
label; rotating coordinates use the actual truncated output. -/
noncomputable def assembleLabel {D : ℕ} {U : Type uU} {V : Type uV}
    (first : Fin D → U) (second : Fin D → Option V) : Option (FullLabel D U V) := by
  classical
  exact if h : ∀ i, ∃ v, second i = some v then
    some (first, fun i => Classical.choose (h i)) else none

theorem assembleLabel_eq_none_iff {D : ℕ} {U : Type uU} {V : Type uV}
    (first : Fin D → U) (second : Fin D → Option V) :
    assembleLabel first second = none ↔ ∃ i, second i = none := by
  classical
  constructor
  · intro ha
    by_contra hn
    have hall : ∀ i, ∃ v, second i = some v := by
      intro i
      cases he : second i with
      | none => exact False.elim (hn ⟨i, he⟩)
      | some v => exact ⟨v, rfl⟩
    simp [assembleLabel, hall] at ha
  · rintro ⟨i, hi⟩
    have hn : ¬ ∀ j, ∃ v, second j = some v := by
      intro hall
      obtain ⟨v, hv⟩ := hall i
      rw [hi] at hv
      cases hv
    simp [assembleLabel, hn]

theorem assembleLabel_some {D : ℕ} {U : Type uU} {V : Type uV}
    (first : Fin D → U) (second : Fin D → V) :
    assembleLabel first (fun i => some (second i)) = some (first, second) := by
  classical
  have hall : ∀ i, ∃ v, some (second i) = some v := fun i => ⟨second i, rfl⟩
  have hchoice : (fun i => Classical.choose (hall i)) = second := by
    funext i
    exact (Option.some.inj (Classical.choose_spec (hall i))).symm
  simpa only [assembleLabel, dite_eq_left hall] using
    congrArg (fun f : Fin D → V => some (first, f)) hchoice

/-- Pointwise reconstruction introduces no independent choice of a mask. -/
noncomputable def assembleWord {D h : ℕ} {U : Type uU} {V : Type uV}
    (first : Fin D → Fin h → U) (second : Fin D → Fin h → Option V) :
    Fin h → Option (FullLabel D U V) :=
  fun z => assembleLabel (fun i => first i z) (fun i => second i z)

theorem assembleWord_dummy_iff {D h : ℕ} {U : Type uU} {V : Type uV}
    (first : Fin D → Fin h → U) (second : Fin D → Fin h → Option V) (z : Fin h) :
    assembleWord first second z = none ↔ ∃ i, second i z = none :=
  assembleLabel_eq_none_iff _ _

/-- All tuples of independently allowed scalar words. Dependent coordinate
types permit first words and truncated second words to have different types. -/
noncomputable def coordinateFamily {n : ℕ} {α : Fin n → Type uAlpha}
    (S : ∀ i, Finset (α i)) : Finset (∀ i, α i) := by
  classical
  exact Fintype.piFinset S

theorem card_coordinateFamily_le {n B : ℕ} {α : Fin n → Type uAlpha}
    (S : ∀ i, Finset (α i)) (hS : ∀ i, (S i).card ≤ B) :
    (coordinateFamily S).card ≤ B ^ n := by
  classical
  rw [coordinateFamily, Fintype.card_piFinset]
  calc
    ∏ i, (S i).card ≤ ∏ _i : Fin n, B :=
      Finset.prod_le_prod (fun i _ => hS i)
    _ = B ^ n := by simp

/-- Arbitrary decoding cannot increase the product count. This applies to
literal full words and to pointwise dummy reconstruction alike. -/
theorem card_decoded_coordinateFamily_le {n B : ℕ} {α : Fin n → Type uAlpha}
    {Word : Type uWord} [DecidableEq Word]
    (S : ∀ i, Finset (α i)) (decode : (∀ i, α i) → Word)
    (hS : ∀ i, (S i).card ≤ B) :
    ((coordinateFamily S).image decode).card ≤ B ^ n :=
  Finset.card_image_le.trans (card_coordinateFamily_le S hS)

/-- The finite union over all rational step vectors and all possible anchor
positions. The scalar families can depend on both, as in the actual re-anchored
breakpoint construction. -/
noncomputable def anchoredFamily {D h : ℕ} {α : Fin (2 * D) → Type uAlpha}
    {Word : Type uWord} [DecidableEq Word]
    (S : (Fin D → Fin h) → Fin h → ∀ i, Finset (α i))
    (decode : (Fin D → Fin h) → Fin h → (∀ i, α i) → Word) : Finset Word := by
  classical
  exact Finset.univ.biUnion fun t => Finset.univ.biUnion fun z =>
    (coordinateFamily (S t z)).image (decode t z)

theorem card_anchoredFamily_le {D h B : ℕ} {α : Fin (2 * D) → Type uAlpha}
    {Word : Type uWord} [DecidableEq Word]
    (S : (Fin D → Fin h) → Fin h → ∀ i, Finset (α i))
    (decode : (Fin D → Fin h) → Fin h → (∀ i, α i) → Word)
    (hS : ∀ t z i, (S t z i).card ≤ B) :
    (anchoredFamily S decode).card ≤ h ^ (D + 1) * B ^ (2 * D) := by
  classical
  unfold anchoredFamily
  calc
    _ ≤ (Finset.univ : Finset (Fin D → Fin h)).card * (h * B ^ (2 * D)) := by
      apply Finset.card_biUnion_le_card_mul
      intro t _
      calc
        _ ≤ (Finset.univ : Finset (Fin h)).card * B ^ (2 * D) := by
          apply Finset.card_biUnion_le_card_mul
          intro z _
          exact card_decoded_coordinateFamily_le (S t z) (decode t z) (hS t z)
        _ = h * B ^ (2 * D) := by simp
    _ = h ^ (D + 1) * B ^ (2 * D) := by
      simp [pow_succ, Nat.mul_assoc]

theorem anchored_polynomial_estimate (D h : ℕ) (hD : 0 < D) (hh : 0 < h) :
    h ^ (D + 1) * (16 * (16004 * D * h + 1) ^ 6) ^ (2 * D) ≤
      (16005 * D * h) ^ (14 * D) := by
  have hDh : 0 < D * h := Nat.mul_pos hD hh
  have hbase : 16004 * D * h + 1 ≤ 16005 * (D * h) := by nlinarith
  have hscalar : 16 * (16004 * D * h + 1) ^ 6 ≤ 16005 ^ 7 * (D * h) ^ 6 := by
    calc
      _ ≤ 16005 * (16005 * (D * h)) ^ 6 :=
        Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hbase 6)
      _ = 16005 ^ 7 * (D * h) ^ 6 := by ring
  have hanchor : h ^ (D + 1) ≤ (D * h) ^ (2 * D) := by
    calc
      _ ≤ (D * h) ^ (D + 1) := Nat.pow_le_pow_left (by nlinarith) _
      _ ≤ (D * h) ^ (2 * D) := Nat.pow_le_pow_right hDh (by omega)
  calc
    _ ≤ (D * h) ^ (2 * D) * (16005 ^ 7 * (D * h) ^ 6) ^ (2 * D) :=
      Nat.mul_le_mul hanchor (Nat.pow_le_pow_left hscalar _)
    _ = 16005 ^ (7 * (2 * D)) * (D * h) ^ (2 * D + 6 * (2 * D)) := by
      rw [mul_pow (16005 ^ 7) ((D * h) ^ 6), ← pow_mul, ← pow_mul,
        mul_left_comm, ← pow_add]
    _ = (16005 * (D * h)) ^ (14 * D) := by
      have h₁ : 7 * (2 * D) = 14 * D := by omega
      have h₂ : 2 * D + 6 * (2 * D) = 14 * D := by omega
      rw [h₁, h₂, mul_pow 16005 (D * h)]
    _ = (16005 * D * h) ^ (14 * D) := by rw [Nat.mul_assoc]

end QuantitativeVanDerWaerden

end OAI
