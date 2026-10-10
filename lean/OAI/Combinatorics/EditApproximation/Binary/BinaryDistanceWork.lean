import OAI.Combinatorics.EditApproximation.Binary.BinaryFiniteLoops
import OAI.Combinatorics.EditApproximation.Probability.FiniteEnumerationWork
import OAI.Combinatorics.EditApproximation.Numerics.RationalPrefix
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Absolute differences used in the literal prefix and band tests.
The sign update retains the magnitude words; subtraction uses signed
Boolean arithmetic. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem absolute_value (a : BinaryFraction) : a.absolute.value = |a.value| := by
  have hn : |(a.numerator.value : ℚ)| = (bitWordValue a.numerator.bits : ℚ) := by
    cases h : a.numerator.negative <;> simp [SignedBinary.value, signedMagnitude, h]
  have hd : (0 : ℚ) < bitWordValue a.denominator := by exact_mod_cast a.denominator_pos
  change (bitWordValue a.numerator.bits : ℚ) / bitWordValue a.denominator =
    |(a.numerator.value : ℚ) / bitWordValue a.denominator|
  rw [abs_div, hn, abs_of_pos hd]

@[simp] theorem absolute_width (a : BinaryFraction) : a.absolute.width = a.width := rfl

@[simp] theorem nat_value (n : ℕ) : (nat n).value = (n : ℚ) := by
  rw [← representation_value, nat_representation, UnreducedRational.value_nat]

theorem canonicalAddWithWork_width (a b : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.canonicalAddWithWork b).1.width ≤ 8 * B + 6 := by
  have hs := UnreducedRational.storageBits_add a.representation b.representation
  have ha' := representation_storageBits_le a
  have hb' := representation_storageBits_le b
  have hw := canonicalAddWithWork_self_width a b
  rw [canonicalAddWithWork_representation] at hw
  omega

theorem subWithWork_width (a b : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.subWithWork b).1.width ≤ 8 * B + 6 := by
  exact canonicalAddWithWork_width a b.neg B ha (by simpa only [neg_width] using hb)



@[simp] theorem distanceWithWork_value (a b : BinaryFraction) :
    (distanceWithWork a b).1.value = |a.value - b.value| := by
  simp only [distanceWithWork, absolute_value, subWithWork_value]

theorem distanceWithWork_width (a b : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (distanceWithWork a b).1.width ≤ 8 * B + 6 :=
  subWithWork_width a b B ha hb

theorem distanceWithWork_cost (a b : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (distanceWithWork a b).2 ≤ 6000 * (B + 1) ^ 2 + 2 := by
  exact Nat.add_le_add_right (subWithWork_cost a b B ha hb) 1

/-- List of the literal endpoint differences. Natural endpoints are encoded
when encountered, and their bit-writing work is charged here. -/


@[simp] theorem connectionTermsWithWork_length {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) :
    (connectionTermsWithWork start states finish).1.length = states.length + 1 := by
  induction states generalizing start with
  | nil => rfl
  | cons state rest ih =>
    simp only [connectionTermsWithWork, List.length_cons, ih]

theorem connectionTermsWithWork_value {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) :
    ((connectionTermsWithWork start states finish).1.map value).sum =
      rationalConnectionBudget start.value states finish.value := by
  induction states generalizing start with
  | nil => simp only [connectionTermsWithWork, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, distanceWithWork_value, rationalConnectionBudget]
  | cons state rest ih =>
    simp only [connectionTermsWithWork, List.map_cons, List.sum_cons,
      distanceWithWork_value, nat_value, ih, rationalConnectionBudget]

theorem connectionTermsWithWork_width {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) (B : ℕ)
    (hs : start.width ≤ B) (hf : finish.width ≤ B)
    (he : ∀ state ∈ states, Nat.size state.lo + 2 ≤ B ∧ Nat.size state.hi + 2 ≤ B) :
    ∀ a ∈ (connectionTermsWithWork start states finish).1, a.width ≤ 8 * B + 6 := by
  induction states generalizing start with
  | nil =>
    intro a ha
    simp only [connectionTermsWithWork, List.mem_singleton] at ha
    subst a
    exact distanceWithWork_width start finish B hs hf
  | cons state rest ih =>
    have hstate := he state List.mem_cons_self
    intro a ha
    simp only [connectionTermsWithWork, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact distanceWithWork_width start (nat state.lo) B hs
        ((nat_width_le state.lo).trans hstate.1)
    · exact ih (nat state.hi) ((nat_width_le state.hi).trans hstate.2)
        (fun s h => he s (List.mem_cons_of_mem _ h)) a ha

 def connectionTermsBitBudget (k B : ℕ) : ℕ :=
  (k + 1) * (6000 * (B + 1) ^ 2 + 4) + k * (2 * B + 6)

theorem connectionTermsWithWork_cost {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) (B : ℕ)
    (hs : start.width ≤ B) (hf : finish.width ≤ B)
    (he : ∀ state ∈ states, Nat.size state.lo + 2 ≤ B ∧ Nat.size state.hi + 2 ≤ B) :
    (connectionTermsWithWork start states finish).2 ≤ connectionTermsBitBudget states.length B := by
  induction states generalizing start with
  | nil =>
    have hc := distanceWithWork_cost start finish B hs hf
    change (distanceWithWork start finish).2 + 2 ≤ _
    simpa only [connectionTermsBitBudget, List.length_nil, zero_add, one_mul, zero_mul,
      add_zero] using Nat.add_le_add_right hc 2
  | cons state rest ih =>
    have hstate := he state List.mem_cons_self
    have hc := distanceWithWork_cost start (nat state.lo) B hs
      ((nat_width_le state.lo).trans hstate.1)
    have ht := ih (nat state.hi) ((nat_width_le state.hi).trans hstate.2)
      (fun s h => he s (List.mem_cons_of_mem _ h))
    change (distanceWithWork start (nat state.lo)).2 +
      (connectionTermsWithWork (nat state.hi) rest finish).2 + Nat.size state.lo +
        Nat.size state.hi + 6 ≤ _
    simp only [connectionTermsBitBudget, List.length_cons] at ht ⊢
    simp only [Nat.add_mul, Nat.one_mul] at ht ⊢
    omega



@[simp] theorem connectionWithWork_value {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) :
    (connectionWithWork start finish states).1.value =
      rationalConnectionBudget start.value states finish.value := by
  simp only [connectionWithWork, sumListWithWork_value, connectionTermsWithWork_value]

def connectionWordBudget (k B : ℕ) : ℕ := bandMassTotalStorageBudget (k + 1) (8 * B + 6)

def connectionBitBudget (k B : ℕ) : ℕ :=
  connectionTermsBitBudget k B + storedSumBitBudget (k + 1) (8 * B + 6) + 6 * (k + 1) + 1

theorem connectionWithWork_width {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) (B : ℕ)
    (hs : start.width ≤ B) (hf : finish.width ≤ B)
    (he : ∀ state ∈ states, Nat.size state.lo + 2 ≤ B ∧ Nat.size state.hi + 2 ≤ B) :
    (connectionWithWork start finish states).1.width ≤ connectionWordBudget states.length B := by
  have h := sumListWithWork_width (connectionTermsWithWork start states finish).1
    (8 * B + 6) (connectionTermsWithWork_width start finish states B hs hf he)
  simpa only [connectionWithWork, connectionTermsWithWork_length, connectionWordBudget] using h

theorem connectionWithWork_cost {n : ℕ} (start finish : BinaryFraction)
    (states : List (TargetInterval n)) (B : ℕ)
    (hs : start.width ≤ B) (hf : finish.width ≤ B)
    (he : ∀ state ∈ states, Nat.size state.lo + 2 ≤ B ∧ Nat.size state.hi + 2 ≤ B) :
    (connectionWithWork start finish states).2 ≤ connectionBitBudget states.length B := by
  have ht := connectionTermsWithWork_cost start finish states B hs hf he
  have hs' := sumListWithWork_cost (connectionTermsWithWork start states finish).1
    (8 * B + 6) (connectionTermsWithWork_width start finish states B hs hf he)
  simp only [connectionTermsWithWork_length] at hs'
  change _ + _ + 1 ≤ _
  unfold connectionBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
