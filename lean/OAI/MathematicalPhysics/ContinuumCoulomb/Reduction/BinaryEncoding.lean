import Mathlib.Data.Nat.Size
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace OAI

/-! Explicit prefix-free binary encodings for finite source and circuit data.
Natural numbers use their binary digits, with one marker bit per digit.
Pairs concatenate; lists have a binary length header. In particular, list
serialization does not repeatedly pair large natural-number codes. -/

namespace ContinuumCoulomb
namespace BinaryEncoding

abbrev BitString := List Bool

structure Codec (α : Type*) where
  encode : α → BitString
  read : BitString → α × BitString
  read_encode : ∀ x tail, read (encode x ++ tail) = (x, tail)

theorem Codec.encode_injective {α : Type*} (c : Codec α) : Function.Injective c.encode := by
  intro x y h
  have hread := congrArg c.read (congrArg (fun s => s ++ []) h)
  rw [c.read_encode, c.read_encode] at hread
  exact congrArg Prod.fst hread

def encodeDigits : BitString → BitString
  | [] => [false]
  | b :: bs => true :: b :: encodeDigits bs

def readDigits : BitString → BitString × BitString
  | true :: b :: bs => let (digits, tail) := readDigits bs; (b :: digits, tail)
  | false :: bs => ([], bs)
  | _ => ([], [])

theorem readDigits_encode (digits tail : BitString) :
    readDigits (encodeDigits digits ++ tail) = (digits, tail) := by
  induction digits with
  | nil => rfl
  | cons b digits ih => simp only [encodeDigits, List.cons_append, readDigits, ih]

def decodeDigits : BitString → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (decodeDigits bs)

theorem decodeDigits_bits (n : ℕ) : decodeDigits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => simp only [Nat.bits_append_bit n b h, decodeDigits, ih]

def natural : Codec ℕ where
  encode n := encodeDigits n.bits
  read s := let (digits, tail) := readDigits s; (decodeDigits digits, tail)
  read_encode n tail := by simp only [readDigits_encode, decodeDigits_bits]

theorem encodeDigits_length (digits : BitString) :
    (encodeDigits digits).length = 2 * digits.length + 1 := by
  induction digits with
  | nil => rfl
  | cons b digits ih => simp only [encodeDigits, List.length_cons, ih]; omega

/-- The code of a natural has linear overhead in its binary bit length. -/
theorem natural_length (n : ℕ) : (natural.encode n).length = 2 * n.size + 1 := by
  change (encodeDigits n.bits).length = _
  rw [encodeDigits_length, Nat.size_eq_bits_len]

/-- Unary electron counts use one true bit per electron and a false terminator. -/
def encodeUnary : ℕ → BitString
  | 0 => [false]
  | n + 1 => true :: encodeUnary n

def readUnary : BitString → ℕ × BitString
  | true :: s => let (n, tail) := readUnary s; (n + 1, tail)
  | false :: s => (0, s)
  | [] => (0, [])

theorem readUnary_encode (n : ℕ) (tail : BitString) :
    readUnary (encodeUnary n ++ tail) = (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [encodeUnary, List.cons_append, readUnary, ih]

def unary : Codec ℕ where
  encode := encodeUnary
  read := readUnary
  read_encode := readUnary_encode

theorem unary_length (n : ℕ) : (unary.encode n).length = n + 1 := by
  change (encodeUnary n).length = n + 1
  induction n with
  | zero => rfl
  | succ n ih => simp only [encodeUnary, List.length_cons, ih]

def integer : Codec ℤ where
  encode
    | Int.ofNat n => false :: natural.encode n
    | Int.negSucc n => true :: natural.encode n
  read
    | false :: s => let (n, tail) := natural.read s; (Int.ofNat n, tail)
    | true :: s => let (n, tail) := natural.read s; (Int.negSucc n, tail)
    | [] => (0, [])
  read_encode z tail := by
    cases z <;> simp only [List.cons_append, natural.read_encode]

def pair {α β : Type*} (a : Codec α) (b : Codec β) : Codec (α × β) where
  encode x := a.encode x.1 ++ b.encode x.2
  read s := let (x, t) := a.read s; let (y, u) := b.read t; ((x, y), u)
  read_encode x tail := by
    rcases x with ⟨x, y⟩
    simp only [List.append_assoc, a.read_encode, b.read_encode]

def readCount {α : Type*} (a : Codec α) : ℕ → BitString → List α × BitString
  | 0, s => ([], s)
  | n + 1, s => let (x, t) := a.read s; let (xs, u) := readCount a n t; (x :: xs, u)

theorem readCount_encode {α : Type*} (a : Codec α) (xs : List α) (tail : BitString) :
    readCount a xs.length (xs.flatMap a.encode ++ tail) = (xs, tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readCount, a.read_encode, ih]

def list {α : Type*} (a : Codec α) : Codec (List α) where
  encode xs := natural.encode xs.length ++ xs.flatMap a.encode
  read s := let (n, t) := natural.read s; readCount a n t
  read_encode xs tail := by
    simp only [List.append_assoc, natural.read_encode, readCount_encode]

def equiv {α β : Type*} (a : Codec α) (e : β ≃ α) : Codec β where
  encode x := a.encode (e x)
  read s := let (x, t) := a.read s; (e.symm x, t)
  read_encode x tail := by simp only [a.read_encode, e.symm_apply_apply]

def sum {α β : Type*} (a : Codec α) (b : Codec β) : Codec (α ⊕ β) where
  encode
    | Sum.inl x => false :: a.encode x
    | Sum.inr y => true :: b.encode y
  read
    | false :: s => let (x, t) := a.read s; (Sum.inl x, t)
    | true :: s => let (y, t) := b.read s; (Sum.inr y, t)
    | [] => let (x, t) := a.read []; (Sum.inl x, t)
  read_encode x tail := by
    cases x <;> simp only [List.cons_append, a.read_encode, b.read_encode]

theorem pair_length {α β : Type*} (a : Codec α) (b : Codec β) (x : α × β) :
    ((pair a b).encode x).length = (a.encode x.1).length + (b.encode x.2).length :=
  List.length_append

theorem list_length {α : Type*} (a : Codec α) (xs : List α) :
    ((list a).encode xs).length = 2 * xs.length.size + 1 +
      (xs.map (fun x => (a.encode x).length)).sum := by
  simp only [list, List.length_append, natural_length, List.length_flatMap]

end BinaryEncoding
end ContinuumCoulomb

end OAI
