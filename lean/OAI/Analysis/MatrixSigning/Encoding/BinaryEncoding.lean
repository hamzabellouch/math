import Mathlib

namespace OAI

section

namespace KS.W01

def frame : List Bool → List Bool
  | [] => [true]
  | b :: bs => false :: b :: frame bs

def unframe : List Bool → Option (List Bool × List Bool)
  | [] => none
  | true :: bs => some ([], bs)
  | false :: [] => none
  | false :: b :: bs => (unframe bs).map (fun p => (b :: p.1, p.2))

@[simp] theorem unframe_frame_append (bs tail : List Bool) :
    unframe (frame bs ++ tail) = some (bs, tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [frame, unframe, ih]

@[simp] theorem length_frame (bs : List Bool) :
    (frame bs).length = 2 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [frame, List.length_cons, ih]; omega

def encodeNat (n : ℕ) : List Bool := frame (Computability.encodeNat n)

def readNat (bs : List Bool) : Option (ℕ × List Bool) :=
  (unframe bs).map (fun p => (Computability.decodeNat p.1, p.2))

@[simp] theorem readNat_encode_append (n : ℕ) (tail : List Bool) :
    readNat (encodeNat n ++ tail) = some (n, tail) := by
  simp [readNat, encodeNat]

def encodeInt : ℤ → List Bool
  | .ofNat n => false :: encodeNat n
  | .negSucc n => true :: encodeNat n

def readInt : List Bool → Option (ℤ × List Bool)
  | [] => none
  | false :: bs => (readNat bs).map (fun p => (Int.ofNat p.1, p.2))
  | true :: bs => (readNat bs).map (fun p => (Int.negSucc p.1, p.2))

@[simp] theorem readInt_encode_append (n : ℤ) (tail : List Bool) :
    readInt (encodeInt n ++ tail) = some (n, tail) := by
  cases n <;> simp [encodeInt, readInt]

def encodeRat (q : ℚ) : List Bool := encodeInt q.num ++ encodeNat q.den

def readRat (bs : List Bool) : Option (ℚ × List Bool) := do
  let (num, rest) ← readInt bs
  let (den, tail) ← readNat rest
  return (mkRat num den, tail)

@[simp] theorem readRat_encode_append (q : ℚ) (tail : List Bool) :
    readRat (encodeRat q ++ tail) = some (q, tail) := by
  simp [readRat, encodeRat, List.append_assoc, Rat.mkRat_self]

abbrev RationalComplex := ℚ × ℚ

def encodeComplex (z : RationalComplex) : List Bool := encodeRat z.1 ++ encodeRat z.2

def readComplex (bs : List Bool) : Option (RationalComplex × List Bool) := do
  let (re, rest) ← readRat bs
  let (im, tail) ← readRat rest
  return ((re, im), tail)

@[simp] theorem readComplex_encode_append (z : RationalComplex) (tail : List Bool) :
    readComplex (encodeComplex z ++ tail) = some (z, tail) := by
  simp [readComplex, encodeComplex, List.append_assoc]

def decodeComplex (bs : List Bool) : Option RationalComplex := do
  let (z, rest) ← readComplex bs
  if rest = [] then some z else none

@[simp] theorem decodeComplex_encode (z : RationalComplex) :
    decodeComplex (encodeComplex z) = some z := by
  have h := readComplex_encode_append z []
  simp only [List.append_nil] at h
  simp [decodeComplex, h]

theorem encodeComplex_injective : Function.Injective encodeComplex := by
  intro z w h
  have := congrArg decodeComplex h
  simpa using this

def natPayloadLength (n : ℕ) : ℕ := (Computability.encodeNat n).length

def intPayload (n : ℤ) : ℕ := match n with
  | .ofNat k => k
  | .negSucc k => k

@[simp] theorem length_encodeNat (n : ℕ) :
    (encodeNat n).length = 2 * natPayloadLength n + 1 := by
  simp [encodeNat, natPayloadLength]

@[simp] theorem length_encodeInt (n : ℤ) :
    (encodeInt n).length = 2 * natPayloadLength (intPayload n) + 2 := by
  cases n <;> simp [encodeInt, intPayload]

@[simp] theorem length_encodeRat (q : ℚ) :
    (encodeRat q).length =
      2 * (natPayloadLength (intPayload q.num) + natPayloadLength q.den) + 3 := by
  simp only [encodeRat, List.length_append, length_encodeInt, length_encodeNat]
  omega

@[simp] theorem length_encodeComplex (z : RationalComplex) :
    (encodeComplex z).length = (encodeRat z.1).length + (encodeRat z.2).length := by
  simp [encodeComplex]

theorem length_encodePosNum (n : PosNum) :
    (Computability.encodePosNum n).length = n.natSize := by
  induction n <;> simp_all [Computability.encodePosNum, PosNum.natSize]

theorem length_encodeNum (n : Num) :
    (Computability.encodeNum n).length = n.natSize := by
  cases n with
  | zero => rfl
  | pos p => exact length_encodePosNum p

@[simp] theorem natPayloadLength_eq_size (n : ℕ) : natPayloadLength n = Nat.size n := by
  unfold natPayloadLength Computability.encodeNat
  rw [length_encodeNum, Num.natSize_to_nat, Num.to_of_nat]

theorem natPayloadLength_le_iff (n k : ℕ) :
    natPayloadLength n ≤ k ↔ n < 2 ^ k := by
  rw [natPayloadLength_eq_size, Nat.size_le]

end KS.W01

end

end OAI
