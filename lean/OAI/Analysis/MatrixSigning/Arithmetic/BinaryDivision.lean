import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.BinaryEncoding

namespace OAI

section

namespace KS.W19

def digit (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem digit_false : digit false = 0 := rfl
@[simp] theorem digit_true : digit true = 1 := rfl

def bitsValue : List Bool → ℕ
  | [] => 0
  | b :: bs => digit b + 2 * bitsValue bs

theorem digit_le_one (b : Bool) : digit b ≤ 1 := by cases b <;> decide

def compareDigit (a b : Bool) : Ordering :=
  if a then (if b then .eq else .gt) else (if b then .lt else .eq)

def compareBits : List Bool → List Bool → Ordering
  | [], [] => .eq
  | [], b :: bs => match compareBits [] bs with
    | .eq => compareDigit false b
    | o => o
  | a :: as, [] => match compareBits as [] with
    | .eq => compareDigit a false
    | o => o
  | a :: as, b :: bs => match compareBits as bs with
    | .eq => compareDigit a b
    | o => o
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

def OrderingCorrect (o : Ordering) (a b : ℕ) : Prop :=
  match o with
  | .lt => a < b
  | .eq => a = b
  | .gt => b < a

theorem compareBits_correct (xs ys : List Bool) :
    OrderingCorrect (compareBits xs ys) (bitsValue xs) (bitsValue ys) := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [compareBits, OrderingCorrect, bitsValue]
    | cons b bs ih =>
      cases hc : compareBits [] bs <;>
        simp only [hc, OrderingCorrect, bitsValue] at ih <;>
        cases b <;> simp [compareBits, hc, compareDigit, OrderingCorrect, bitsValue, digit] <;> omega
  | cons a as ih =>
    cases ys with
    | nil =>
      have h := ih []
      cases hc : compareBits as [] <;>
        simp only [hc, OrderingCorrect, bitsValue] at h <;>
        cases a <;> simp [compareBits, hc, compareDigit, OrderingCorrect, bitsValue, digit] <;> omega
    | cons b bs =>
      have h := ih bs
      cases hc : compareBits as bs <;>
        simp only [hc, OrderingCorrect] at h <;>
        cases a <;> cases b <;>
        simp [compareBits, hc, compareDigit, OrderingCorrect, bitsValue, digit] <;> omega

theorem compareBits_lt_iff (xs ys : List Bool) :
    compareBits xs ys = .lt ↔ bitsValue xs < bitsValue ys := by
  have h := compareBits_correct xs ys
  cases hc : compareBits xs ys <;> simp [hc, OrderingCorrect] at h ⊢ <;> omega

def differenceDigit (a b borrow : Bool) : Bool := Bool.xor (Bool.xor a b) borrow

def nextBorrow (a b borrow : Bool) : Bool :=
  (!a && (b || borrow)) || (b && borrow)

theorem subtraction_column (a b c : Bool) :
    digit a + 2 * digit (nextBorrow a b c) =
      digit (differenceDigit a b c) + digit b + digit c := by
  cases a <;> cases b <;> cases c <;> decide

def subtractBits : List Bool → List Bool → Bool → List Bool
  | [], [], _ => []
  | [], b :: bs, c => differenceDigit false b c :: subtractBits [] bs (nextBorrow false b c)
  | a :: as, [], c => differenceDigit a false c :: subtractBits as [] (nextBorrow a false c)
  | a :: as, b :: bs, c => differenceDigit a b c :: subtractBits as bs (nextBorrow a b c)
termination_by xs ys _ => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

private theorem tail_borrow_le (a b c : Bool) (x y : ℕ)
    (h : digit b + 2 * y + digit c ≤ digit a + 2 * x) :
    y + digit (nextBorrow a b c) ≤ x := by
  have he := subtraction_column a b c
  have ho := digit_le_one (differenceDigit a b c)
  omega

private theorem subtraction_lift (a b c : Bool) (x y r : ℕ)
    (hr : r + y + digit (nextBorrow a b c) = x) :
    (digit (differenceDigit a b c) + 2 * r) + (digit b + 2 * y) + digit c =
      digit a + 2 * x := by
  have he := subtraction_column a b c
  omega

theorem subtractBits_correct (xs ys : List Bool) (c : Bool)
    (h : bitsValue ys + digit c ≤ bitsValue xs) :
    bitsValue (subtractBits xs ys c) + bitsValue ys + digit c = bitsValue xs := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil =>
      simp only [bitsValue, Nat.zero_add] at h
      simpa [subtractBits, bitsValue] using Nat.eq_zero_of_le_zero h
    | cons b bs ih =>
      have ht := tail_borrow_le false b c 0 (bitsValue bs) (by simpa [bitsValue, digit] using h)
      have hr := ih (nextBorrow false b c) (by simpa [bitsValue] using ht)
      have hh := subtraction_lift false b c 0 (bitsValue bs)
        (bitsValue (subtractBits [] bs (nextBorrow false b c))) (by simpa [bitsValue] using hr)
      simpa [subtractBits, bitsValue, digit] using hh
  | cons a as ih =>
    cases ys with
    | nil =>
      have ht := tail_borrow_le a false c (bitsValue as) 0 (by simpa [bitsValue, digit] using h)
      have hr := ih [] (nextBorrow a false c) (by simpa [bitsValue] using ht)
      have hh := subtraction_lift a false c (bitsValue as) 0
        (bitsValue (subtractBits as [] (nextBorrow a false c))) (by simpa [bitsValue] using hr)
      simpa [subtractBits, bitsValue, digit] using hh
    | cons b bs =>
      have ht := tail_borrow_le a b c (bitsValue as) (bitsValue bs) (by simpa [bitsValue] using h)
      have hr := ih bs (nextBorrow a b c) ht
      simpa only [subtractBits, bitsValue] using
        subtraction_lift a b c (bitsValue as) (bitsValue bs)
          (bitsValue (subtractBits as bs (nextBorrow a b c))) hr

theorem subtractBits_length (xs ys : List Bool) (c : Bool) :
    (subtractBits xs ys c).length = max xs.length ys.length := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subtractBits]
    | cons b bs ih => simp [subtractBits, ih]
  | cons a as ih =>
    cases ys with
    | nil => simp [subtractBits, ih]
    | cons b bs => simp only [subtractBits, List.length_cons, ih]; omega

def divideBits (divisor : List Bool) : List Bool → List Bool × List Bool
  | [] => ([], [])
  | b :: bs =>
    let qr := divideBits divisor bs
    let trial := b :: qr.2
    if compareBits trial divisor = .lt then
      (false :: qr.1, trial)
    else
      (true :: qr.1, subtractBits trial divisor false)

theorem divideBits_correct (divisor xs : List Bool) (hd : 0 < bitsValue divisor) :
    bitsValue xs = bitsValue divisor * bitsValue (divideBits divisor xs).1 +
      bitsValue (divideBits divisor xs).2 ∧
    bitsValue (divideBits divisor xs).2 < bitsValue divisor := by
  induction xs with
  | nil => simpa [divideBits, bitsValue] using hd
  | cons b bs ih =>
    have hb := digit_le_one b
    by_cases hc : compareBits (b :: (divideBits divisor bs).2) divisor = .lt
    · have hl := (compareBits_lt_iff _ _).mp hc
      simp only [divideBits, hc, ↓reduceIte]
      simp only [bitsValue, digit_false, Nat.zero_add] at hl ⊢
      constructor
      · nlinarith [ih.1]
      · exact hl
    · have hle : bitsValue divisor ≤ bitsValue (b :: (divideBits divisor bs).2) := by
        exact Nat.le_of_not_gt (fun h => hc ((compareBits_lt_iff _ _).mpr h))
      have hs := subtractBits_correct (b :: (divideBits divisor bs).2) divisor false
        (by simpa [digit] using hle)
      simp only [digit_false, Nat.add_zero] at hs
      simp only [divideBits, hc, ↓reduceIte, bitsValue, digit_true]
      simp only [bitsValue] at hs
      constructor
      · nlinarith [ih.1]
      · nlinarith [ih.2]

theorem divideBits_quotient_length (divisor xs : List Bool) :
    (divideBits divisor xs).1.length = xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [divideBits]; split <;> simp [ih]

theorem divideBits_remainder_length (divisor xs : List Bool) :
    (divideBits divisor xs).2.length ≤ xs.length + divisor.length := by
  induction xs with
  | nil => simp [divideBits]
  | cons b bs ih =>
    simp only [divideBits]
    split
    · simp only [List.length_cons]
      omega
    · simp only [subtractBits_length, List.length_cons]
      omega

theorem bitsValue_encodePosNum (n : PosNum) :
    bitsValue (Computability.encodePosNum n) = (n : ℕ) := by
  induction n <;> simp_all [Computability.encodePosNum, bitsValue, digit, PosNum.cast_bit0,
    PosNum.cast_bit1] <;> omega

theorem bitsValue_encodeNum (n : Num) :
    bitsValue (Computability.encodeNum n) = (n : ℕ) := by
  cases n with
  | zero => rfl
  | pos p => exact bitsValue_encodePosNum p

theorem bitsValue_encodeNat (n : ℕ) : bitsValue (Computability.encodeNat n) = n := by
  unfold Computability.encodeNat
  rw [bitsValue_encodeNum, Num.to_of_nat]

theorem divideBits_encodeNat_correct (n d : ℕ) (hd : 0 < d) :
    let qr := divideBits (Computability.encodeNat d) (Computability.encodeNat n)
    n = d * bitsValue qr.1 + bitsValue qr.2 ∧ bitsValue qr.2 < d := by
  simpa only [bitsValue_encodeNat] using
    divideBits_correct (Computability.encodeNat d) (Computability.encodeNat n)
      (by simpa only [bitsValue_encodeNat] using hd)

def bitScanCost : List Bool → List Bool → ℕ
  | [], [] => 1
  | [], _ :: ys => bitScanCost [] ys + 1
  | _ :: xs, [] => bitScanCost xs [] + 1
  | _ :: xs, _ :: ys => bitScanCost xs ys + 1
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

theorem bitScanCost_eq (xs ys : List Bool) :
    bitScanCost xs ys = max xs.length ys.length + 1 := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [bitScanCost]
    | cons b bs ih => simp [bitScanCost, ih]
  | cons a as ih =>
    cases ys with
    | nil => simp [bitScanCost, ih]
    | cons b bs => simp only [bitScanCost, List.length_cons, ih]; omega

def divisionIterations : List Bool → ℕ
  | [] => 0
  | _ :: xs => divisionIterations xs + 1

theorem divisionIterations_eq_length (xs : List Bool) : divisionIterations xs = xs.length := by
  induction xs <;> simp_all [divisionIterations]

def divisionBitCost (divisor : List Bool) : List Bool → ℕ
  | [] => 1
  | b :: bs =>
    let qr := divideBits divisor bs
    let trial := b :: qr.2
    divisionBitCost divisor bs + 1 + bitScanCost trial divisor +
      if compareBits trial divisor = .lt then 0 else bitScanCost trial divisor

theorem divisionBitCost_le (divisor xs : List Bool) :
    divisionBitCost divisor xs ≤
      xs.length * (xs.length + 4 * divisor.length + 4) + 1 := by
  induction xs with
  | nil => simp [divisionBitCost]
  | cons b bs ih =>
    have hr := divideBits_remainder_length divisor bs
    have hs : bitScanCost (b :: (divideBits divisor bs).2) divisor ≤
        bs.length + 2 * divisor.length + 2 := by
      rw [bitScanCost_eq]
      simp only [List.length_cons]
      omega
    simp only [divisionBitCost, List.length_cons]
    split <;> nlinarith

theorem divideBits_output_length_le (divisor xs : List Bool) :
    (divideBits divisor xs).1.length + (divideBits divisor xs).2.length ≤
      2 * xs.length + divisor.length := by
  rw [divideBits_quotient_length]
  have h := divideBits_remainder_length divisor xs
  omega

theorem encodeNat_length_eq_size (n : ℕ) : (Computability.encodeNat n).length = Nat.size n :=
  KS.W01.natPayloadLength_eq_size n

theorem divisionBitCost_encodeNat_le (n d : ℕ) :
    divisionBitCost (Computability.encodeNat d) (Computability.encodeNat n) ≤
      Nat.size n * (Nat.size n + 4 * Nat.size d + 4) + 1 := by
  simpa only [encodeNat_length_eq_size] using
    divisionBitCost_le (Computability.encodeNat d) (Computability.encodeNat n)

def signedBitsValue (negative : Bool) (xs : List Bool) : ℤ :=
  if negative then Int.negSucc (bitsValue xs) else Int.ofNat (bitsValue xs)

def divideSignedBits (negative : Bool) (divisor xs : List Bool) : List Bool × List Bool :=
  let qr := divideBits divisor xs
  if negative then
    (qr.1, subtractBits (subtractBits divisor [true] false) qr.2 false)
  else qr

theorem divideSignedBits_correct (negative : Bool) (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    signedBitsValue negative xs = (bitsValue divisor : ℤ) *
      signedBitsValue negative (divideSignedBits negative divisor xs).1 +
        (bitsValue (divideSignedBits negative divisor xs).2 : ℤ) ∧
    bitsValue (divideSignedBits negative divisor xs).2 < bitsValue divisor := by
  have hu := divideBits_correct divisor xs hd
  have hc : (bitsValue xs : ℤ) = (bitsValue divisor : ℤ) *
      (bitsValue (divideBits divisor xs).1 : ℤ) +
        (bitsValue (divideBits divisor xs).2 : ℤ) := by exact_mod_cast hu.1
  cases negative
  · simpa [divideSignedBits, signedBitsValue] using And.intro hc hu.2
  · have hp : bitsValue (subtractBits divisor [true] false) + 1 = bitsValue divisor := by
      have hh := subtractBits_correct divisor [true] false (by simp [bitsValue, digit]; omega)
      simpa [bitsValue, digit] using hh
    have hr : bitsValue (divideBits divisor xs).2 ≤ bitsValue (subtractBits divisor [true] false) := by
      omega
    have hs : bitsValue (subtractBits (subtractBits divisor [true] false)
        (divideBits divisor xs).2 false) + bitsValue (divideBits divisor xs).2 =
          bitsValue (subtractBits divisor [true] false) := by
      simpa only [digit_false, Nat.add_zero] using
        subtractBits_correct (subtractBits divisor [true] false) (divideBits divisor xs).2 false
          (by simpa only [digit_false, Nat.add_zero] using hr)
    have hsn : bitsValue (subtractBits (subtractBits divisor [true] false)
        (divideBits divisor xs).2 false) + bitsValue (divideBits divisor xs).2 + 1 =
          bitsValue divisor := by omega
    have hsi : (bitsValue (subtractBits (subtractBits divisor [true] false)
        (divideBits divisor xs).2 false) : ℤ) + (bitsValue (divideBits divisor xs).2 : ℤ) + 1 =
          (bitsValue divisor : ℤ) := by exact_mod_cast hsn
    have he : -((bitsValue xs : ℤ) + 1) = (bitsValue divisor : ℤ) *
        (-((bitsValue (divideBits divisor xs).1 : ℤ) + 1)) +
          (bitsValue (subtractBits (subtractBits divisor [true] false)
            (divideBits divisor xs).2 false) : ℤ) := by nlinarith
    have hl : bitsValue (subtractBits (subtractBits divisor [true] false)
        (divideBits divisor xs).2 false) < bitsValue divisor := by omega
    simpa [divideSignedBits, signedBitsValue, Int.negSucc_eq, Nat.cast_add] using And.intro he hl

theorem divideSignedBits_output_length_le (negative : Bool) (divisor xs : List Bool) :
    (divideSignedBits negative divisor xs).1.length +
      (divideSignedBits negative divisor xs).2.length ≤ 2 * xs.length + divisor.length + 1 := by
  have hq := divideBits_quotient_length divisor xs
  have hr := divideBits_remainder_length divisor xs
  cases negative
  · simpa only [divideSignedBits, Bool.false_eq_true, ↓reduceIte] using
      (divideBits_output_length_le divisor xs).trans (Nat.le_succ _)
  · simp only [divideSignedBits, ↓reduceIte, subtractBits_length, List.length_cons,
      List.length_nil, hq]
    omega

theorem divideSignedBits_quotient (negative : Bool) (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    signedBitsValue negative (divideSignedBits negative divisor xs).1 =
      signedBitsValue negative xs / (bitsValue divisor : ℤ) := by
  have h := divideSignedBits_correct negative divisor xs hd
  have hp : (0 : ℤ) < bitsValue divisor := by exact_mod_cast hd
  have hr : (bitsValue (divideSignedBits negative divisor xs).2 : ℤ) <
      (bitsValue divisor : ℤ) := by exact_mod_cast h.2
  have hz : (0 : ℤ) ≤ bitsValue (divideSignedBits negative divisor xs).2 := Nat.cast_nonneg _
  symm
  apply (Int.ediv_eq_iff_of_pos hp).mpr
  constructor <;> nlinarith [h.1]

def signedDivisionBitCost (negative : Bool) (divisor xs : List Bool) : ℕ :=
  divisionBitCost divisor xs +
    if negative then bitScanCost divisor [true] +
      bitScanCost (subtractBits divisor [true] false) (divideBits divisor xs).2
    else 0

theorem signedDivisionBitCost_le (negative : Bool) (divisor xs : List Bool) :
    signedDivisionBitCost negative divisor xs ≤
      xs.length * (xs.length + 4 * divisor.length + 4) + xs.length + 3 * divisor.length + 5 := by
  have hu := divisionBitCost_le divisor xs
  have hr := divideBits_remainder_length divisor xs
  have hs₁ : bitScanCost divisor [true] ≤ divisor.length + 2 := by
    rw [bitScanCost_eq]
    simp only [List.length_cons, List.length_nil]
    omega
  have hs₂ : bitScanCost (subtractBits divisor [true] false) (divideBits divisor xs).2 ≤
      xs.length + 2 * divisor.length + 2 := by
    rw [bitScanCost_eq, subtractBits_length]
    simp only [List.length_cons, List.length_nil]
    omega
  cases negative <;> simp only [signedDivisionBitCost, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem signedDivisionBitCost_quadratic (negative : Bool) (divisor xs : List Bool) :
    signedDivisionBitCost negative divisor xs ≤ 6 * (xs.length + divisor.length + 1) ^ 2 := by
  have h := signedDivisionBitCost_le negative divisor xs
  nlinarith

def negativeOfInt : ℤ → Bool
  | .ofNat _ => false
  | .negSucc _ => true

theorem signedBitsValue_intPayload (z : ℤ) :
    signedBitsValue (negativeOfInt z) (Computability.encodeNat (KS.W01.intPayload z)) = z := by
  cases z <;> simp [negativeOfInt, signedBitsValue, KS.W01.intPayload, bitsValue_encodeNat]

theorem divideSignedBits_intPayload_quotient (z : ℤ) (d : ℕ) (hd : 0 < d) :
    signedBitsValue (negativeOfInt z)
      (divideSignedBits (negativeOfInt z) (Computability.encodeNat d)
        (Computability.encodeNat (KS.W01.intPayload z))).1 = z / (d : ℤ) := by
  simpa only [bitsValue_encodeNat, signedBitsValue_intPayload] using
    divideSignedBits_quotient (negativeOfInt z) (Computability.encodeNat d)
      (Computability.encodeNat (KS.W01.intPayload z)) (by simpa only [bitsValue_encodeNat] using hd)

end KS.W19

end

end OAI
