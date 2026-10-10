import OAI.Combinatorics.EditApproximation.Binary.BinaryDivisionWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryCanonicalWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Fresh Boolean-list cells allocated by the literal arithmetic routines.
Input tails are shared. Counts include discarded intermediate lists, so they
also bound the cells simultaneously live during evaluation. -/

namespace EditApproximation





theorem bitAddAllocation_le_work (left right : List Bool) (carry : Bool) :
    bitAddAllocation left right carry ≤ (bitAddWithWork left right carry).2 := by
  induction left generalizing right carry with
  | nil =>
    simp only [bitAddAllocation, bitAddWithWork]
    induction right generalizing carry with
    | nil => cases carry <;> simp [bitAddNilLeftAllocation, bitAddNilLeftWithWork]
    | cons b bs ih =>
      have h := ih (bitCarry false b carry)
      simp only [bitAddNilLeftAllocation, bitAddNilLeftWithWork]
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih [] (bitCarry a false carry)
      simp only [bitAddAllocation, bitAddWithWork]
      omega
    | cons b bs =>
      have h := ih bs (bitCarry a b carry)
      simp only [bitAddAllocation, bitAddWithWork]
      omega





theorem bitSubtractAllocation_le_work (left right : List Bool) (borrow : Bool) :
    bitSubtractAllocation left right borrow ≤ (bitSubtractWithWork left right borrow).2.2 := by
  induction left generalizing right borrow with
  | nil =>
    simp only [bitSubtractAllocation, bitSubtractWithWork]
    induction right generalizing borrow with
    | nil => simp [bitSubtractNilLeftAllocation, bitSubtractNilLeftWithWork]
    | cons b bs ih =>
      have h := ih (bitBorrow false b borrow)
      simp only [bitSubtractNilLeftAllocation, bitSubtractNilLeftWithWork]
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih [] (bitBorrow a false borrow)
      simp only [bitSubtractAllocation, bitSubtractWithWork]
      omega
    | cons b bs =>
      have h := ih bs (bitBorrow a b borrow)
      simp only [bitSubtractAllocation, bitSubtractWithWork]
      omega



theorem bitMulAllocation_le_work (left right : List Bool) :
    bitMulAllocation left right ≤ (bitMulWithWork left right).2 := by
  induction left with
  | nil => simp [bitMulAllocation, bitMulWithWork]
  | cons bit bits ih =>
    have h := bitAddAllocation_le_work (false :: (bitMulWithWork bits right).1) right false
    cases bit <;> simp only [bitMulAllocation, bitMulWithWork, Bool.false_eq_true, ↓reduceIte] <;>
      omega



theorem trimBitWordAllocation_le_work (bits : List Bool) :
    trimBitWordAllocation bits ≤ (trimBitWordWithWork bits).2 := by
  induction bits with
  | nil => simp [trimBitWordAllocation, trimBitWordWithWork]
  | cons bit bits ih =>
    simp only [trimBitWordAllocation, trimBitWordWithWork]
    split_ifs <;> omega

/-- Each division step allocates one candidate cell and one quotient cell,
plus the fresh subtraction result exactly when subtraction is executed. -/


theorem bitDivModAllocation_le_work (divisor bits : List Bool) :
    bitDivModAllocation divisor bits ≤ (bitDivModWithWork divisor bits).2.2 := by
  induction bits with
  | nil => simp [bitDivModAllocation, bitDivModWithWork]
  | cons bit bits ih =>
    have h := bitSubtractAllocation_le_work
      (bit :: (bitDivModWithWork divisor bits).2.1) divisor false
    simp only [bitDivModAllocation, bitDivModWithWork]
    split_ifs <;> dsimp only <;> omega

/-- Comparison allocates no Boolean-list cells. The recursive frames have
height at most the explicitly charged work counter. -/
theorem bitCompare_recursion_le_work (left right : List Bool) :
    max left.length right.length + 1 ≤ (bitCompareWithWork left right).2 := by
  induction left generalizing right with
  | nil =>
    simp only [bitCompareWithWork]
    induction right with
    | nil => simp [bitCompareNilLeftWithWork]
    | cons b bs ih =>
      simp only [bitCompareNilLeftWithWork, List.length_nil, List.length_cons, Nat.zero_max] at *
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih []
      simp only [bitCompareWithWork, List.length_nil, List.length_cons, Nat.max_zero] at *
      omega
    | cons b bs =>
      have h := ih bs
      simp only [bitCompareWithWork, List.length_cons, Nat.succ_max_succ]
      omega

end EditApproximation

end OAI
