import OAI.Combinatorics.EditApproximation.Numerics.ScalarAllocation

namespace OAI

/-! Invocation counts for literal Boolean routines. An active call stack is a
subset of these invocations. Each frame has a fixed number of bit/word/pointer
fields, so these bounds complement (rather than replace) fresh-array storage. -/

namespace EditApproximation

def bitAddInvocations : List Bool → List Bool → Bool → ℕ
  | [], [], _ => 1
  | a :: as, [], carry => bitAddInvocations as [] (bitCarry a false carry) + 1
  | [], b :: bs, carry => bitAddInvocations [] bs (bitCarry false b carry) + 1
  | a :: as, b :: bs, carry => bitAddInvocations as bs (bitCarry a b carry) + 1

theorem bitAddInvocations_le_work (left right : List Bool) (carry : Bool) :
    bitAddInvocations left right carry ≤ (bitAddWithWork left right carry).2 := by
  induction left generalizing right carry with
  | nil =>
    simp only [bitAddWithWork]
    induction right generalizing carry with
    | nil => simp [bitAddInvocations, bitAddNilLeftWithWork]
    | cons b bs ih =>
      have h := ih (bitCarry false b carry)
      simp only [bitAddInvocations, bitAddNilLeftWithWork]
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih [] (bitCarry a false carry)
      simp only [bitAddInvocations, bitAddWithWork]
      omega
    | cons b bs =>
      have h := ih bs (bitCarry a b carry)
      simp only [bitAddInvocations, bitAddWithWork]
      omega

def bitSubtractInvocations : List Bool → List Bool → Bool → ℕ
  | [], [], _ => 1
  | a :: as, [], borrow => bitSubtractInvocations as [] (bitBorrow a false borrow) + 1
  | [], b :: bs, borrow => bitSubtractInvocations [] bs (bitBorrow false b borrow) + 1
  | a :: as, b :: bs, borrow => bitSubtractInvocations as bs (bitBorrow a b borrow) + 1

theorem bitSubtractInvocations_le_work (left right : List Bool) (borrow : Bool) :
    bitSubtractInvocations left right borrow ≤ (bitSubtractWithWork left right borrow).2.2 := by
  induction left generalizing right borrow with
  | nil =>
    simp only [bitSubtractWithWork]
    induction right generalizing borrow with
    | nil => simp [bitSubtractInvocations, bitSubtractNilLeftWithWork]
    | cons b bs ih =>
      have h := ih (bitBorrow false b borrow)
      simp only [bitSubtractInvocations, bitSubtractNilLeftWithWork]
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih [] (bitBorrow a false borrow)
      simp only [bitSubtractInvocations, bitSubtractWithWork]
      omega
    | cons b bs =>
      have h := ih bs (bitBorrow a b borrow)
      simp only [bitSubtractInvocations, bitSubtractWithWork]
      omega

def bitCompareInvocations (left right : List Bool) : ℕ := max left.length right.length + 1

theorem bitCompareInvocations_le_work (left right : List Bool) :
    bitCompareInvocations left right ≤ (bitCompareWithWork left right).2 :=
  bitCompare_recursion_le_work left right

def bitMulInvocations : List Bool → List Bool → ℕ
  | [], _ => 1
  | bit :: bits, right =>
    bitMulInvocations bits right + 1 +
      if bit then bitAddInvocations (false :: (bitMulWithWork bits right).1) right false else 0

theorem bitMulInvocations_le_work (left right : List Bool) :
    bitMulInvocations left right ≤ (bitMulWithWork left right).2 := by
  induction left with
  | nil => rfl
  | cons bit bits ih =>
    have h := bitAddInvocations_le_work (false :: (bitMulWithWork bits right).1) right false
    cases bit <;> simp only [bitMulInvocations, bitMulWithWork, Bool.false_eq_true, ↓reduceIte] <;> omega

def trimBitWordInvocations (bits : List Bool) : ℕ := bits.length + 1

theorem trimBitWordInvocations_le_work (bits : List Bool) :
    trimBitWordInvocations bits ≤ (trimBitWordWithWork bits).2 := by
  rw [trimBitWordWithWork_cost]
  unfold trimBitWordInvocations
  omega

def bitDivModInvocations (divisor : List Bool) : List Bool → ℕ
  | [] => 1
  | bit :: bits =>
    let candidate := bit :: (bitDivModWithWork divisor bits).2.1
    bitDivModInvocations divisor bits + bitCompareInvocations candidate divisor + 1 +
      if (bitCompareWithWork candidate divisor).1 = .lt then 0
      else bitSubtractInvocations candidate divisor false

theorem bitDivModInvocations_le_work (divisor bits : List Bool) :
    bitDivModInvocations divisor bits ≤ (bitDivModWithWork divisor bits).2.2 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    have hc := bitCompareInvocations_le_work (bit :: (bitDivModWithWork divisor bits).2.1) divisor
    have hs := bitSubtractInvocations_le_work (bit :: (bitDivModWithWork divisor bits).2.1) divisor false
    simp only [bitDivModInvocations, bitDivModWithWork]
    split_ifs <;> dsimp only <;> omega

def bitPowerInvocations (base : List Bool) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    let previous := (bitPowerWithWork base n).1
    bitPowerInvocations base n + bitMulInvocations previous base +
      trimBitWordInvocations (bitMulWithWork previous base).1 + 1

theorem bitPowerInvocations_le_work (base : List Bool) (n : ℕ) :
    bitPowerInvocations base n ≤ (bitPowerWithWork base n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hm := bitMulInvocations_le_work (bitPowerWithWork base n).1 base
    have ht := trimBitWordInvocations_le_work (bitMulWithWork (bitPowerWithWork base n).1 base).1
    simp only [bitPowerInvocations, bitPowerWithWork]
    omega

end EditApproximation

end OAI
