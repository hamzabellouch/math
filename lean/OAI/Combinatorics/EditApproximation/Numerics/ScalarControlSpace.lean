import OAI.Combinatorics.EditApproximation.Binary.FractionControlSpace

namespace OAI

namespace EditApproximation

def bitCeilDivInvocations (divisor bits : List Bool) : ℕ :=
  let divided := bitDivModWithWork divisor bits
  bitDivModInvocations divisor bits + bitCompareInvocations divided.2.1 [] + 1 +
    if (bitCompareWithWork divided.2.1 []).1 = .eq then 0
    else bitAddInvocations divided.1 [true] false

theorem bitCeilDivInvocations_le_work (divisor bits : List Bool) :
    bitCeilDivInvocations divisor bits ≤ (bitCeilDivWithWork divisor bits).2 := by
  have hd := bitDivModInvocations_le_work divisor bits
  have hc := bitCompareInvocations_le_work (bitDivModWithWork divisor bits).2.1 []
  have ha := bitAddInvocations_le_work (bitDivModWithWork divisor bits).1 [true] false
  unfold bitCeilDivInvocations bitCeilDivWithWork
  dsimp only
  split_ifs <;> dsimp only <;> omega

def coarseDenominatorInvocations (allowanceDen q L branching : List Bool) (D : ℕ) : ℕ :=
  let first := bitMulWithWork L branching
  let base := bitMulWithWork first.1 q
  let trimmed := trimBitWordWithWork base.1
  let power := bitPowerWithWork trimmed.1 D
  let initial := bitMulWithWork allowanceDen q
  let product := bitMulWithWork initial.1 power.1
  bitMulInvocations L branching + bitMulInvocations first.1 q + trimBitWordInvocations base.1 +
    bitPowerInvocations trimmed.1 D + bitMulInvocations allowanceDen q +
    bitMulInvocations initial.1 power.1 + trimBitWordInvocations product.1 + 1

theorem coarseDenominatorInvocations_le_work (allowanceDen q L branching : List Bool) (D : ℕ) :
    coarseDenominatorInvocations allowanceDen q L branching D ≤
      (coarseDenominatorWithWork allowanceDen q L branching D).2 := by
  have h1 := bitMulInvocations_le_work L branching
  have h2 := bitMulInvocations_le_work (bitMulWithWork L branching).1 q
  have h3 := trimBitWordInvocations_le_work (bitMulWithWork (bitMulWithWork L branching).1 q).1
  have h4 := bitPowerInvocations_le_work
    (trimBitWordWithWork (bitMulWithWork (bitMulWithWork L branching).1 q).1).1 D
  have h5 := bitMulInvocations_le_work allowanceDen q
  have h6 := bitMulInvocations_le_work (bitMulWithWork allowanceDen q).1
    (bitPowerWithWork (trimBitWordWithWork (bitMulWithWork (bitMulWithWork L branching).1 q).1).1 D).1
  have h7 := trimBitWordInvocations_le_work
    (bitMulWithWork (bitMulWithWork allowanceDen q).1
      (bitPowerWithWork (trimBitWordWithWork (bitMulWithWork (bitMulWithWork L branching).1 q).1).1 D).1).1
  unfold coarseDenominatorInvocations coarseDenominatorWithWork
  dsimp only
  omega

/-- Includes the map's base frame and every recursive traversal frame. -/
def arithmeticMapInvocations {α : Type*} (invocations : α → ℕ) : List α → ℕ
  | [] => 1
  | a :: rest => invocations a + arithmeticMapInvocations invocations rest + 1

theorem arithmeticMapInvocations_le_work {α β : Type*} (f : α → β × ℕ)
    (invocations : α → ℕ) (values : List α)
    (h : ∀ a ∈ values, invocations a ≤ (f a).2) :
    arithmeticMapInvocations invocations values ≤ (arithmeticMapWithWork f values).2 + 1 := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    have hh := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [arithmeticMapInvocations, arithmeticMapWithWork]
    omega

namespace BinaryFraction

def invInvocations (a : BinaryFraction) : ℕ := bitCompareInvocations a.numerator.bits [] + 1

theorem invInvocations_le_work (a : BinaryFraction) :
    invInvocations a ≤ a.invWithWork.2 := by
  have h := bitCompareInvocations_le_work a.numerator.bits []
  unfold invInvocations invWithWork
  dsimp only
  split_ifs <;> dsimp only <;> omega

def divInvocations (a b : BinaryFraction) : ℕ :=
  invInvocations b + canonicalMulInvocations a b.invWithWork.1 + 1

theorem divInvocations_le_work (a b : BinaryFraction) :
    divInvocations a b ≤ (divWithWork a b).2 := by
  have hi := invInvocations_le_work b
  have hm := canonicalMulInvocations_le_work a b.invWithWork.1
  unfold divInvocations divWithWork
  dsimp only
  omega

def fixedDenominatorInvocations (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) : ℕ :=
  let product := bitMulWithWork a.numerator.bits denominator
  let quotient := bitDivModWithWork a.denominator product.1
  let raw : BinaryFraction := ⟨⟨a.numerator.negative, quotient.1⟩, denominator, hden⟩
  bitMulInvocations a.numerator.bits denominator + bitDivModInvocations a.denominator product.1 +
    canonicalizeInvocations raw + 1

theorem fixedDenominatorInvocations_le_work (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) :
    fixedDenominatorInvocations a denominator hden ≤ (fixedDenominatorWithWork a denominator hden).2 := by
  have hm := bitMulInvocations_le_work a.numerator.bits denominator
  have hd := bitDivModInvocations_le_work a.denominator
    (bitMulWithWork a.numerator.bits denominator).1
  have hc := canonicalizeInvocations_le_work
    (⟨⟨a.numerator.negative,
      (bitDivModWithWork a.denominator (bitMulWithWork a.numerator.bits denominator).1).1⟩,
      denominator, hden⟩ : BinaryFraction)
  unfold fixedDenominatorInvocations fixedDenominatorWithWork
  dsimp only
  omega

def naturalCeilingInvocations (a : BinaryFraction) : ℕ :=
  if a.numerator.negative then 1 else bitCeilDivInvocations a.denominator a.numerator.bits + 1

theorem naturalCeilingInvocations_le_work (a : BinaryFraction) :
    naturalCeilingInvocations a ≤ a.naturalCeilingWithWork.2 := by
  have h := bitCeilDivInvocations_le_work a.denominator a.numerator.bits
  unfold naturalCeilingInvocations naturalCeilingWithWork
  split_ifs <;> dsimp only <;> omega

end BinaryFraction
end EditApproximation

end OAI
