import OAI.Combinatorics.EditApproximation.Binary.FractionAllocation
import OAI.Combinatorics.EditApproximation.Binary.BinaryFixedDenominator
import OAI.Combinatorics.EditApproximation.Binary.BinaryCeilingWork
import OAI.Combinatorics.EditApproximation.Coarse.CoarseDenominatorArithmetic
import OAI.Combinatorics.EditApproximation.Probability.FiniteEnumerationWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



theorem bitPowerAllocation_le_work (base : List Bool) (n : ℕ) :
    bitPowerAllocation base n ≤ (bitPowerWithWork base n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hm := bitMulAllocation_le_work (bitPowerWithWork base n).1 base
    have ht := trimBitWordAllocation_le_work
      (bitMulWithWork (bitPowerWithWork base n).1 base).1
    simp only [bitPowerAllocation, bitPowerWithWork]
    omega

def coarseDenominatorAllocation (allowanceDen q L branching : List Bool) (D : ℕ) : ℕ :=
  let first := bitMulWithWork L branching
  let base := bitMulWithWork first.1 q
  let trimmed := trimBitWordWithWork base.1
  let power := bitPowerWithWork trimmed.1 D
  let initial := bitMulWithWork allowanceDen q
  let product := bitMulWithWork initial.1 power.1
  bitMulAllocation L branching + bitMulAllocation first.1 q + trimBitWordAllocation base.1 +
    bitPowerAllocation trimmed.1 D + bitMulAllocation allowanceDen q +
    bitMulAllocation initial.1 power.1 + trimBitWordAllocation product.1

theorem coarseDenominatorAllocation_le_work (allowanceDen q L branching : List Bool) (D : ℕ) :
    coarseDenominatorAllocation allowanceDen q L branching D ≤
      (coarseDenominatorWithWork allowanceDen q L branching D).2 := by
  have h1 := bitMulAllocation_le_work L branching
  have h2 := bitMulAllocation_le_work (bitMulWithWork L branching).1 q
  have h3 := trimBitWordAllocation_le_work (bitMulWithWork (bitMulWithWork L branching).1 q).1
  have h4 := bitPowerAllocation_le_work
    (trimBitWordWithWork (bitMulWithWork (bitMulWithWork L branching).1 q).1).1 D
  have h5 := bitMulAllocation_le_work allowanceDen q
  have h6 := bitMulAllocation_le_work (bitMulWithWork allowanceDen q).1
    (bitPowerWithWork (trimBitWordWithWork (bitMulWithWork (bitMulWithWork L branching).1 q).1).1 D).1
  have h7 := trimBitWordAllocation_le_work
    (bitMulWithWork (bitMulWithWork allowanceDen q).1
      (bitPowerWithWork (trimBitWordWithWork (bitMulWithWork (bitMulWithWork L branching).1 q).1).1 D).1).1
  unfold coarseDenominatorAllocation coarseDenominatorWithWork
  dsimp only
  omega



theorem bitCeilDivAllocation_le_work (divisor bits : List Bool) :
    bitCeilDivAllocation divisor bits ≤ (bitCeilDivWithWork divisor bits).2 := by
  have hd := bitDivModAllocation_le_work divisor bits
  have ha := bitAddAllocation_le_work (bitDivModWithWork divisor bits).1 [true] false
  unfold bitCeilDivAllocation bitCeilDivWithWork
  dsimp only
  split_ifs <;> dsimp only <;> omega

/-- Map allocation includes one result spine cell for every callback. -/


theorem arithmeticMapAllocation_le_work {α β : Type*} (f : α → β × ℕ)
    (allocation : α → ℕ) (values : List α)
    (h : ∀ a ∈ values, allocation a ≤ (f a).2) :
    arithmeticMapAllocation allocation values ≤ (arithmeticMapWithWork f values).2 := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    have hh := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [arithmeticMapAllocation, arithmeticMapWithWork]
    omega

namespace BinaryFraction



theorem invAllocation_le_work (a : BinaryFraction) :
    invAllocation a ≤ a.invWithWork.2 := by
  unfold invAllocation invWithWork
  dsimp only
  split_ifs <;> dsimp only
  · exact Nat.succ_le_succ (Nat.zero_le _)
  · exact Nat.zero_le _



theorem divAllocation_le_work (a b : BinaryFraction) :
    divAllocation a b ≤ (divWithWork a b).2 := by
  have hi := invAllocation_le_work b
  have hm := canonicalMulAllocation_le_work a b.invWithWork.1
  unfold divAllocation divWithWork
  dsimp only
  omega



theorem fixedDenominatorAllocation_le_work (a : BinaryFraction) (denominator : List Bool)
    (hden : 0 < bitWordValue denominator) :
    fixedDenominatorAllocation a denominator hden ≤ (fixedDenominatorWithWork a denominator hden).2 := by
  have hm := bitMulAllocation_le_work a.numerator.bits denominator
  have hd := bitDivModAllocation_le_work a.denominator
    (bitMulWithWork a.numerator.bits denominator).1
  have hc := canonicalizeAllocation_le_work
    (⟨⟨a.numerator.negative,
      (bitDivModWithWork a.denominator (bitMulWithWork a.numerator.bits denominator).1).1⟩,
      denominator, hden⟩ : BinaryFraction)
  unfold fixedDenominatorAllocation fixedDenominatorWithWork
  dsimp only
  omega



theorem naturalCeilingAllocation_le_work (a : BinaryFraction) :
    naturalCeilingAllocation a ≤ a.naturalCeilingWithWork.2 := by
  have h := bitCeilDivAllocation_le_work a.denominator a.numerator.bits
  unfold naturalCeilingAllocation naturalCeilingWithWork
  split_ifs <;> dsimp only <;> omega

end BinaryFraction
end EditApproximation

end OAI
