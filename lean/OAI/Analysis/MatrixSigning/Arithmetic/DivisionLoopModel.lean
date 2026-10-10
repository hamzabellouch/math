import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.SubtractionBorrow

namespace OAI

section

namespace KS.W19.DivisionLoop
open KS.W19

def advance (divisor : List Bool) (b : Bool) (q r : List Bool) : List Bool × List Bool :=
  let trial := b :: r
  if subtractionBorrow trial divisor false then (false :: q, trial)
  else (true :: q, trimBits (subtractBits trial divisor false))

theorem advance_correct (divisor : List Bool) (b : Bool) (q r : List Bool)
    (hd : 0 < bitsValue divisor) (hr : bitsValue r < bitsValue divisor) :
    bitsValue divisor * bitsValue (advance divisor b q r).1 +
        bitsValue (advance divisor b q r).2 =
      2 * (bitsValue divisor * bitsValue q + bitsValue r) + digit b ∧
      bitsValue (advance divisor b q r).2 < bitsValue divisor := by
  have hb := digit_le_one b
  by_cases hc : subtractionBorrow (b :: r) divisor false = true
  · have hlt := (subtractionBorrow_true_iff _ _ _).1 hc
    simp only [digit_false, Nat.add_zero] at hlt
    simp only [advance, hc, ↓reduceIte, bitsValue, digit_false, Nat.zero_add]
    constructor
    · ring
    · exact hlt
  · have hle : bitsValue divisor ≤ bitsValue (b :: r) := by
      apply Nat.le_of_not_gt
      intro hlt
      apply hc
      exact (subtractionBorrow_true_iff (b :: r) divisor false).2
        (by simpa only [digit_false, Nat.add_zero] using hlt)
    have hs := subtractBits_correct (b :: r) divisor false (by simpa only [digit_false, Nat.add_zero] using hle)
    simp only [digit_false, Nat.add_zero, bitsValue] at hs
    simp only [advance, hc, Bool.false_eq_true, ↓reduceIte, trimBits_value, bitsValue, digit_true]
    constructor
    · nlinarith
    · apply (Nat.lt_iff_le_pred hd).2
      omega

def process (divisor : List Bool) : List Bool → List Bool → List Bool → List Bool × List Bool
  | [], q, r => (q,r)
  | b :: bs, q, r =>
    let qr := advance divisor b q r
    process divisor bs qr.1 qr.2

theorem bitsValue_append_digit (xs : List Bool) (b : Bool) :
    bitsValue (xs ++ [b]) = bitsValue xs + digit b * 2 ^ xs.length := by
  induction xs with
  | nil => simp [bitsValue]
  | cons a as ih => simp [bitsValue, ih, pow_succ]; ring

theorem process_correct (divisor pending q r : List Bool)
    (hd : 0 < bitsValue divisor) (hr : bitsValue r < bitsValue divisor) :
    bitsValue divisor * bitsValue (process divisor pending q r).1 +
        bitsValue (process divisor pending q r).2 =
      (bitsValue divisor * bitsValue q + bitsValue r) * 2 ^ pending.length +
        bitsValue pending.reverse ∧
      bitsValue (process divisor pending q r).2 < bitsValue divisor := by
  induction pending generalizing q r with
  | nil => simpa [process, bitsValue] using hr
  | cons b bs ih =>
    have ha := advance_correct divisor b q r hd hr
    have ht := ih (advance divisor b q r).1 (advance divisor b q r).2 ha.2
    simp only [process]
    constructor
    · rw [ht.1, ha.1]
      simp only [List.length_cons, List.reverse_cons, bitsValue_append_digit, List.length_reverse, pow_succ]
      ring
    · exact ht.2

theorem process_payload_correct (divisor xs : List Bool) (hd : 0 < bitsValue divisor) :
    let qr := process divisor xs.reverse [] []
    bitsValue xs = bitsValue divisor * bitsValue qr.1 + bitsValue qr.2 ∧
      bitsValue qr.2 < bitsValue divisor := by
  have h := process_correct divisor xs.reverse [] [] hd (by simpa only [bitsValue] using hd)
  simp only [bitsValue, Nat.mul_zero, Nat.zero_add, Nat.zero_mul, List.reverse_reverse] at h
  exact ⟨h.1.symm, h.2⟩

theorem advance_quotient_length (divisor : List Bool) (b : Bool) (q r : List Bool) :
    (advance divisor b q r).1.length = q.length + 1 := by
  unfold advance
  dsimp only
  split <;> rfl

theorem advance_remainder_length (divisor : List Bool) (b : Bool) (q r : List Bool) :
    (advance divisor b q r).2.length ≤ max (r.length + 1) divisor.length := by
  unfold advance
  dsimp only
  split
  · simp only [List.length_cons]
    omega
  · exact (trimBits_length_le _).trans (by rw [subtractBits_length]; rfl)

theorem process_quotient_length (d pending q r : List Bool) :
    (process d pending q r).1.length = q.length + pending.length := by
  induction pending generalizing q r with
  | nil => simp [process]
  | cons b bs ih =>
    simp only [process, ih, advance_quotient_length, List.length_cons]
    omega

theorem process_remainder_length (d pending q r : List Bool) :
    (process d pending q r).2.length ≤ max r.length d.length + pending.length := by
  induction pending generalizing q r with
  | nil => simp only [process, List.length_nil, Nat.add_zero]; omega
  | cons b bs ih =>
    have ht := ih (advance d b q r).1 (advance d b q r).2
    have hr := advance_remainder_length d b q r
    simp only [process, List.length_cons]
    omega

end KS.W19.DivisionLoop

end

end OAI
