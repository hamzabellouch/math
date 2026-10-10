import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.Reductions.BinaryTokenMachine

namespace OAI

namespace BinPackingGap.BinaryArithmetic

abbrev bitValue := BinPackingCompleteness.BinaryEncoding.bitsValue

@[simp] theorem bitValue_nil : bitValue [] = 0 := rfl

@[simp] theorem bitValue_cons (b : Bool) (bs : List Bool) :
    bitValue (b :: bs) = Nat.bit b (bitValue bs) := rfl

@[simp] theorem bitValue_bits (n : Nat) : bitValue n.bits = n :=
  BinPackingCompleteness.BinaryEncoding.bitsValue_bits n

def Canonical : List Bool → Prop
  | [] => True
  | b :: bs => Canonical bs ∧ (bs = [] → b = true)

theorem bitValue_eq_zero_iff {bs : List Bool} (h : Canonical bs) :
    bitValue bs = 0 ↔ bs = [] := by
  revert h
  induction bs with
  | nil => intro h; simp
  | cons b bs ih =>
      intro h
      constructor
      · intro hz
        have htail : bitValue bs = 0 := by
          cases b <;> simp [Nat.bit] at hz
          omega
        have hnil := (ih h.1).mp htail
        have hb := h.2 hnil
        simp [hnil, hb, Nat.bit] at hz
      · intro hn
        cases hn

theorem canonical_bits (n : Nat) : Canonical n.bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [Canonical]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      refine ⟨ih, ?_⟩
      intro hnil
      apply hn
      have h := congrArg bitValue hnil
      simpa using h

theorem bits_bitValue {bs : List Bool} (h : Canonical bs) :
    (bitValue bs).bits = bs := by
  revert h
  induction bs with
  | nil => intro h; simp
  | cons b bs ih =>
      intro h
      have hn : bitValue bs = 0 → b = true :=
        fun hz => h.2 ((bitValue_eq_zero_iff h.1).mp hz)
      rw [bitValue_cons, Nat.bits_append_bit _ _ hn, ih h.1]

theorem canonical_length {bs : List Bool} (h : Canonical bs) :
    bs.length = (bitValue bs).size := by
  have hlen := congrArg List.length (bits_bitValue h)
  simpa only [Nat.size_eq_bits_len] using hlen.symm

def sumBit (a b c : Bool) : Bool := (a != b) != c

def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

def addCarry : List Bool → List Bool → Bool → List Bool
  | [], [], c => if c then [true] else []
  | a :: as, [], c =>
      sumBit a false c :: addCarry as [] (carryBit a false c)
  | [], b :: bs, c =>
      sumBit false b c :: addCarry [] bs (carryBit false b c)
  | a :: as, b :: bs, c =>
      sumBit a b c :: addCarry as bs (carryBit a b c)
termination_by xs ys _ => xs.length + ys.length
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem bitValue_addCarry (xs ys : List Bool) (c : Bool) :
    bitValue (addCarry xs ys c) =
      bitValue xs + bitValue ys + (if c then 1 else 0) := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [addCarry, Nat.bit]
      | cons b bs ih =>
          cases b <;> cases c <;>
            simp [addCarry, sumBit, carryBit, Nat.bit, ih]
          omega
  | cons a as ih =>
      cases ys with
      | nil =>
          cases a <;> cases c <;>
            simp [addCarry, sumBit, carryBit, Nat.bit, ih]
          omega
      | cons b bs =>
          cases a <;> cases b <;> cases c <;>
            simp [addCarry, sumBit, carryBit, Nat.bit, ih] <;> omega

@[simp] theorem addCarry_eq_nil (xs ys : List Bool) (c : Bool) :
    addCarry xs ys c = [] ↔ xs = [] ∧ ys = [] ∧ c = false := by
  cases xs <;> cases ys <;> cases c <;> simp [addCarry]

theorem canonical_addCarry {xs ys : List Bool} (hx : Canonical xs)
    (hy : Canonical ys) (c : Bool) : Canonical (addCarry xs ys c) := by
  revert hx hy
  induction xs generalizing ys c with
  | nil =>
      intro hx hy
      revert hy
      induction ys generalizing c with
      | nil => intro hy; cases c <;> simp [addCarry, Canonical]
      | cons b bs ih =>
          intro hy
          simp only [addCarry, Canonical]
          refine ⟨ih (c := carryBit false b c) hy.1, ?_⟩
          intro hn
          obtain ⟨_, hbs, hc⟩ := (addCarry_eq_nil _ _ _).mp hn
          have hb := hy.2 hbs
          cases b <;> cases c <;> simp_all [sumBit, carryBit]
  | cons a as ih =>
      intro hx hy
      cases ys with
      | nil =>
          simp only [addCarry, Canonical]
          refine ⟨ih (ys := []) (c := carryBit a false c) hx.1 hy, ?_⟩
          intro hn
          obtain ⟨has, _, hc⟩ := (addCarry_eq_nil _ _ _).mp hn
          have ha := hx.2 has
          cases a <;> cases c <;> simp_all [sumBit, carryBit]
      | cons b bs =>
          simp only [addCarry, Canonical]
          refine ⟨ih (ys := bs) (c := carryBit a b c) hx.1 hy.1, ?_⟩
          intro hn
          obtain ⟨has, hbs, hc⟩ := (addCarry_eq_nil _ _ _).mp hn
          have ha := hx.2 has
          have hb := hy.2 hbs
          cases a <;> cases b <;> cases c <;> simp_all [carryBit]

theorem addCarry_bits (a b : Nat) :
    addCarry a.bits b.bits false = (a + b).bits := by
  have h := bits_bitValue (canonical_addCarry (canonical_bits a) (canonical_bits b) false)
  simpa [bitValue_addCarry] using h.symm

theorem addCarry_length (xs ys : List Bool) (c : Bool) :
    (addCarry xs ys c).length ≤ max xs.length ys.length + 1 := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [addCarry]
      | cons b bs ih =>
          have ht := ih (carryBit false b c)
          simp only [addCarry, List.length_cons, List.length_nil] at ht ⊢
          omega
  | cons a as ih =>
      cases ys with
      | nil =>
          have ht := ih [] (carryBit a false c)
          simp only [addCarry, List.length_cons, List.length_nil] at ht ⊢
          omega
      | cons b bs =>
          have ht := ih bs (carryBit a b c)
          simp only [addCarry, List.length_cons] at ht ⊢
          omega

theorem size_add_le (a b : Nat) :
    (a + b).size ≤ max a.size b.size + 1 := by
  have h := addCarry_length a.bits b.bits false
  simpa [addCarry_bits, Nat.size_eq_bits_len] using h

theorem size_mul_le (a b : Nat) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem size_pow_le (a t : Nat) : (a ^ t).size ≤ t * a.size + 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.pow_succ]
      calc
        (a ^ t * a).size ≤ (a ^ t).size + a.size := size_mul_le _ _
        _ ≤ (t * a.size + 1) + a.size := Nat.add_le_add_right ih _
        _ = (t + 1) * a.size + 1 := by
          simp only [Nat.add_mul, Nat.one_mul]
          omega

def shift (xs : List Bool) : List Bool :=
  if xs = [] then [] else false :: xs

@[simp] theorem bitValue_shift (xs : List Bool) :
    bitValue (shift xs) = 2 * bitValue xs := by
  cases xs <;> simp [shift, Nat.bit]

theorem canonical_shift {xs : List Bool} (hx : Canonical xs) :
    Canonical (shift xs) := by
  cases xs with
  | nil => simp [shift, Canonical]
  | cons b bs => simpa [shift, Canonical] using hx

theorem shift_length_le (xs : List Bool) : (shift xs).length ≤ xs.length + 1 := by
  cases xs <;> simp [shift]

theorem shift_bits (a : Nat) : shift a.bits = (2 * a).bits := by
  have h := bits_bitValue (canonical_shift (canonical_bits a))
  simpa using h.symm

def mulAcc (xs : List Bool) : List Bool → List Bool → List Bool
  | [], acc => acc
  | b :: ys, acc =>
      mulAcc (shift xs) ys (if b then addCarry xs acc false else acc)

theorem bitValue_mulAcc (xs ys acc : List Bool) :
    bitValue (mulAcc xs ys acc) = bitValue xs * bitValue ys + bitValue acc := by
  induction ys generalizing xs acc with
  | nil => simp [mulAcc]
  | cons b ys ih =>
      cases b <;> simp [mulAcc, ih, bitValue_addCarry, Nat.bit] <;> ring

theorem canonical_mulAcc {xs ys acc : List Bool} (hx : Canonical xs)
    (ha : Canonical acc) : Canonical (mulAcc xs ys acc) := by
  revert hx ha
  induction ys generalizing xs acc with
  | nil => intro hx ha; exact ha
  | cons b ys ih =>
      intro hx ha
      simp only [mulAcc]
      apply ih (canonical_shift hx)
      cases b
      · exact ha
      · exact canonical_addCarry hx ha false

theorem mulAcc_bits (a b : Nat) : mulAcc a.bits b.bits [] = (a * b).bits := by
  have h := bits_bitValue (canonical_mulAcc (ys := b.bits) (canonical_bits a)
    (show Canonical [] from trivial))
  simpa [bitValue_mulAcc] using h.symm

theorem mulAcc_bits_length (a b : Nat) :
    (mulAcc a.bits b.bits []).length ≤ a.size + b.size := by
  simpa [mulAcc_bits, Nat.size_eq_bits_len] using size_mul_le a b

def powTally (base : List Bool) : List Bool → List Bool
  | [] => [true]
  | _ :: tally => mulAcc base (powTally base tally) []

theorem bitValue_powTally (base tally : List Bool) :
    bitValue (powTally base tally) = bitValue base ^ tally.length := by
  induction tally with
  | nil => simp [powTally, Nat.bit]
  | cons token tally ih =>
      simp [powTally, bitValue_mulAcc, ih, Nat.pow_succ, Nat.mul_comm]

theorem canonical_powTally {base : List Bool} (hb : Canonical base) (tally : List Bool) :
    Canonical (powTally base tally) := by
  cases tally with
  | nil => simp [powTally, Canonical]
  | cons token tally =>
      exact canonical_mulAcc hb (show Canonical [] from trivial)

theorem powTally_bits (a : Nat) (tally : List Bool) :
    powTally a.bits tally = (a ^ tally.length).bits := by
  have h := bits_bitValue (canonical_powTally (canonical_bits a) tally)
  simpa [bitValue_powTally] using h.symm

theorem powTally_bits_length (a : Nat) (tally : List Bool) :
    (powTally a.bits tally).length ≤ tally.length * a.size + 1 := by
  simpa [powTally_bits, Nat.size_eq_bits_len] using size_pow_le a tally.length

def powAcc (base : List Bool) : List Bool → List Bool → List Bool
  | [], acc => acc
  | _ :: tally, acc => powAcc base tally (mulAcc base acc [])

theorem bitValue_powAcc (base tally acc : List Bool) :
    bitValue (powAcc base tally acc) =
      bitValue base ^ tally.length * bitValue acc := by
  induction tally generalizing acc with
  | nil => simp [powAcc]
  | cons token tally ih =>
      simp [powAcc, ih, bitValue_mulAcc, Nat.pow_succ, Nat.mul_assoc]

theorem canonical_powAcc {base acc : List Bool} (hb : Canonical base)
    (ha : Canonical acc) (tally : List Bool) : Canonical (powAcc base tally acc) := by
  induction tally generalizing acc with
  | nil => exact ha
  | cons token tally ih =>
      apply ih
      exact canonical_mulAcc hb (show Canonical [] from trivial)

theorem powAcc_bits (a r : Nat) (tally : List Bool) :
    powAcc a.bits tally r.bits = (a ^ tally.length * r).bits := by
  have h := bits_bitValue (canonical_powAcc (canonical_bits a) (canonical_bits r) tally)
  simpa [bitValue_powAcc] using h.symm

theorem powAcc_bits_length (a r : Nat) (tally : List Bool) :
    (powAcc a.bits tally r.bits).length ≤ tally.length * a.size + r.size + 1 := by
  rw [powAcc_bits, Nat.size_eq_bits_len]
  have hm := size_mul_le (a ^ tally.length) r
  have hp := size_pow_le a tally.length
  omega

theorem powAcc_bits_length_take (a r k : Nat) (tally : List Bool) :
    (powAcc a.bits (tally.take k) r.bits).length ≤ k * a.size + r.size + 1 := by
  have h := powAcc_bits_length a r (tally.take k)
  have ht : (tally.take k).length ≤ k := by simp
  have hm := Nat.mul_le_mul_right a.size ht
  omega

def consBit : Bool → List Bool → List Bool
  | false, [] => []
  | b, bs => b :: bs

@[simp] theorem bitValue_consBit (b : Bool) (bs : List Bool) :
    bitValue (consBit b bs) = Nat.bit b (bitValue bs) := by
  cases b <;> cases bs <;> rfl

theorem canonical_consBit (b : Bool) {bs : List Bool} (h : Canonical bs) :
    Canonical (consBit b bs) := by
  cases bs with
  | nil => cases b <;> simp [consBit, Canonical]
  | cons a as => cases b <;> exact ⟨h, by simp⟩

theorem consBit_length_le (b : Bool) (bs : List Bool) :
    (consBit b bs).length ≤ bs.length + 1 := by
  cases b <;> cases bs <;> simp [consBit]

def trim : List Bool → List Bool
  | [] => []
  | b :: bs => consBit b (trim bs)

@[simp] theorem bitValue_trim (bs : List Bool) : bitValue (trim bs) = bitValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [trim, ih]

theorem canonical_trim (bs : List Bool) : Canonical (trim bs) := by
  induction bs with
  | nil => trivial
  | cons b bs ih => exact canonical_consBit b ih

theorem trim_eq_bits (bs : List Bool) : trim bs = (bitValue bs).bits := by
  have h := bits_bitValue (canonical_trim bs)
  simpa using h.symm

theorem trim_length_le (bs : List Bool) : (trim bs).length ≤ bs.length := by
  induction bs with
  | nil => simp [trim]
  | cons b bs ih =>
      have hc := consBit_length_le b (trim bs)
      simp only [trim, List.length_cons]
      omega

def trimHigh : List Bool → List Bool
  | [] => []
  | false :: bs => trimHigh bs
  | true :: bs => true :: bs

theorem trimHigh_append (xs ys : List Bool) :
    trimHigh (xs ++ ys) =
      if trimHigh xs = [] then trimHigh ys else trimHigh xs ++ ys := by
  induction xs with
  | nil => simp [trimHigh]
  | cons b xs ih =>
      cases b with
      | false =>
          change trimHigh (xs ++ ys) =
            if trimHigh xs = [] then trimHigh ys else trimHigh xs ++ ys
          exact ih
      | true => simp [trimHigh]

theorem trimHigh_reverse (bs : List Bool) :
    trimHigh bs.reverse = (trim bs).reverse := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      rw [List.reverse_cons, trimHigh_append, ih]
      cases ht : trim bs with
      | nil => cases b <;> simp [trim, ht, consBit, trimHigh]
      | cons d ds => cases b <;> simp [trim, ht, consBit, List.reverse_cons]

theorem trimHigh_length_le (bs : List Bool) : (trimHigh bs).length ≤ bs.length := by
  induction bs with
  | nil => simp [trimHigh]
  | cons b bs ih =>
      cases b <;> simp [trimHigh]
      omega

def diffBit (a b c : Bool) : Bool := (a != b) != c

def borrowBit (a b c : Bool) : Bool := ((!a) && (b || c)) || (b && c)

def subBorrow : List Bool → List Bool → Bool → Option (List Bool)
  | [], [], c => if c then none else some []
  | a :: as, [], c =>
      (subBorrow as [] (borrowBit a false c)).map (fun bs => diffBit a false c :: bs)
  | [], b :: bs, c =>
      (subBorrow [] bs (borrowBit false b c)).map (fun ds => diffBit false b c :: ds)
  | a :: as, b :: bs, c =>
      (subBorrow as bs (borrowBit a b c)).map (fun ds => diffBit a b c :: ds)
termination_by xs ys _ => xs.length + ys.length
decreasing_by
  all_goals simp_wf
  all_goals omega

def rawSubtract : List Bool → List Bool → Bool → List Bool × Bool
  | [], [], c => ([], c)
  | a :: as, [], c =>
      let r := rawSubtract as [] (borrowBit a false c)
      (diffBit a false c :: r.1, r.2)
  | [], b :: bs, c =>
      let r := rawSubtract [] bs (borrowBit false b c)
      (diffBit false b c :: r.1, r.2)
  | a :: as, b :: bs, c =>
      let r := rawSubtract as bs (borrowBit a b c)
      (diffBit a b c :: r.1, r.2)
termination_by xs ys _ => xs.length + ys.length
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem subBorrow_eq_rawSubtract (xs ys : List Bool) (c : Bool) :
    subBorrow xs ys c =
      if (rawSubtract xs ys c).2 then none else some (rawSubtract xs ys c).1 := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [subBorrow, rawSubtract]
      | cons b bs ih =>
          simp only [subBorrow, rawSubtract]
          rw [ih]
          cases rawSubtract [] bs (borrowBit false b c) with
          | mk ds borrow => cases borrow <;> rfl
  | cons a as ih =>
      cases ys with
      | nil =>
          simp only [subBorrow, rawSubtract]
          rw [ih]
          cases rawSubtract as [] (borrowBit a false c) with
          | mk ds borrow => cases borrow <;> rfl
      | cons b bs =>
          simp only [subBorrow, rawSubtract]
          rw [ih]
          cases rawSubtract as bs (borrowBit a b c) with
          | mk ds borrow => cases borrow <;> rfl

theorem rawSubtract_length (xs ys : List Bool) (c : Bool) :
    (rawSubtract xs ys c).1.length = max xs.length ys.length := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => simp [rawSubtract]
      | cons b bs ih =>
          have ht := ih (borrowBit false b c)
          simp only [rawSubtract, List.length_cons, List.length_nil] at ht ⊢
          omega
  | cons a as ih =>
      cases ys with
      | nil =>
          have ht := ih [] (borrowBit a false c)
          simp only [rawSubtract, List.length_cons, List.length_nil] at ht ⊢
          omega
      | cons b bs =>
          have ht := ih bs (borrowBit a b c)
          simp only [rawSubtract, List.length_cons] at ht ⊢
          omega

def BorrowSpec (m n : Nat) (c : Bool) : Option (List Bool) → Prop
  | none => m < n + (if c then 1 else 0)
  | some zs => bitValue zs + n + (if c then 1 else 0) = m

theorem borrowSpec_step (a b c : Bool) (m n : Nat) (r : Option (List Bool))
    (h : BorrowSpec m n (borrowBit a b c) r) :
    BorrowSpec (Nat.bit a m) (Nat.bit b n) c
      (r.map (fun ds => diffBit a b c :: ds)) := by
  cases r with
  | none =>
      change m < n + (if borrowBit a b c then 1 else 0) at h
      change Nat.bit a m < Nat.bit b n + (if c then 1 else 0)
      cases a <;> cases b <;> cases c <;>
        simp [borrowBit, Nat.bit] at h ⊢ <;> omega
  | some zs =>
      change bitValue zs + n + (if borrowBit a b c then 1 else 0) = m at h
      change bitValue (diffBit a b c :: zs) + Nat.bit b n +
        (if c then 1 else 0) = Nat.bit a m
      cases a <;> cases b <;> cases c <;>
        simp [diffBit, borrowBit, Nat.bit] at h ⊢ <;> omega

theorem subBorrow_spec (xs ys : List Bool) (c : Bool) :
    BorrowSpec (bitValue xs) (bitValue ys) c (subBorrow xs ys c) := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [subBorrow, BorrowSpec]
      | cons b bs ih =>
          simpa [subBorrow, Nat.bit] using
            borrowSpec_step false b c 0 (bitValue bs)
              (subBorrow [] bs (borrowBit false b c))
              (ih (borrowBit false b c))
  | cons a as ih =>
      cases ys with
      | nil =>
          simpa [subBorrow, Nat.bit] using
            borrowSpec_step a false c (bitValue as) 0
              (subBorrow as [] (borrowBit a false c))
              (ih [] (borrowBit a false c))
      | cons b bs =>
          simpa [subBorrow] using
            borrowSpec_step a b c (bitValue as) (bitValue bs)
              (subBorrow as bs (borrowBit a b c))
              (ih bs (borrowBit a b c))

theorem subBorrow_none_iff (xs ys : List Bool) (c : Bool) :
    subBorrow xs ys c = none ↔ bitValue xs < bitValue ys + (if c then 1 else 0) := by
  have h := subBorrow_spec xs ys c
  cases hr : subBorrow xs ys c with
  | none => simpa [hr, BorrowSpec] using h
  | some zs =>
      have he : bitValue zs + bitValue ys + (if c then 1 else 0) = bitValue xs := by
        simpa [hr, BorrowSpec] using h
      simp only [Option.some_ne_none, false_iff]
      omega

theorem subBorrow_some_value {xs ys zs : List Bool} {c : Bool}
    (h : subBorrow xs ys c = some zs) :
    bitValue zs + bitValue ys + (if c then 1 else 0) = bitValue xs := by
  simpa [h, BorrowSpec] using subBorrow_spec xs ys c

def monus (xs ys : List Bool) : List Bool := trim ((subBorrow xs ys false).getD [])

theorem bitValue_monus (xs ys : List Bool) :
    bitValue (monus xs ys) = bitValue xs - bitValue ys := by
  have h := subBorrow_spec xs ys false
  cases hr : subBorrow xs ys false with
  | none =>
      have hlt : bitValue xs < bitValue ys := by simpa [hr, BorrowSpec] using h
      simp [monus, hr]
      omega
  | some zs =>
      have he : bitValue zs + bitValue ys = bitValue xs := by
        simpa [hr, BorrowSpec] using h
      have hv : bitValue zs = bitValue xs - bitValue ys := by omega
      simpa [monus, hr] using hv

theorem canonical_monus (xs ys : List Bool) : Canonical (monus xs ys) :=
  canonical_trim _

theorem monus_bits (a b : Nat) : monus a.bits b.bits = (a - b).bits := by
  have h := bits_bitValue (canonical_monus a.bits b.bits)
  simpa [bitValue_monus] using h.symm

theorem size_monus_le (a b : Nat) : (a - b).size ≤ a.size :=
  Nat.size_le_size (Nat.sub_le a b)

theorem monus_bits_length (a b : Nat) :
    (monus a.bits b.bits).length ≤ a.size := by
  simpa [monus_bits, Nat.size_eq_bits_len] using size_monus_le a b

end BinPackingGap.BinaryArithmetic

namespace BinPackingGap.UnaryToBinaryMachine

open Turing BinPackingGames.Foundations.Complexity
open MachineComposition BinaryArithmetic
open BinPackingGames.Reduction.MachineTransfer

def increment : List Bool → List Bool
  | [] => [true]
  | false :: bits => true :: bits
  | true :: bits => false :: increment bits

theorem increment_ne_nil (bits : List Bool) : increment bits ≠ [] := by
  cases bits with
  | nil => simp [increment]
  | cons bit bits => cases bit <;> simp [increment]

theorem bitValue_increment (bits : List Bool) :
    bitValue (increment bits) = bitValue bits + 1 := by
  induction bits with
  | nil => simp [increment, Nat.bit]
  | cons bit bits ih =>
      cases bit <;> simp [increment, Nat.bit, ih]
      omega

theorem canonical_increment {bits : List Bool} (h : Canonical bits) :
    Canonical (increment bits) := by
  revert h
  induction bits with
  | nil => intro h; simp [increment, Canonical]
  | cons bit bits ih =>
      intro h
      cases bit with
      | false => exact ⟨h.1, fun _ => rfl⟩
      | true => exact ⟨ih h.1, fun hnil => False.elim (increment_ne_nil bits hnil)⟩

theorem increment_bits (n : Nat) : increment n.bits = (n + 1).bits := by
  have h := bits_bitValue (canonical_increment (canonical_bits n))
  simpa only [bitValue_increment, bitValue_bits] using h.symm

def incrementCost : List Bool → Nat
  | [] => 2
  | false :: _ => 2
  | true :: bits => incrementCost bits + 2

theorem incrementCost_le (bits : List Bool) :
    incrementCost bits ≤ 2 * bits.length + 2 := by
  induction bits with
  | nil => simp [incrementCost]
  | cons bit bits ih =>
      cases bit <;> simp [incrementCost]
      omega

private theorem size_le_self (n : Nat) : n.size ≤ n := by
  apply Nat.size_le.mpr
  exact n.lt_two_pow_self

def steps : Nat → Nat → Nat
  | 0, _ => 1
  | n + 1, initial => 1 + incrementCost initial.bits + steps n (initial + 1)

theorem steps_le (n initial : Nat) :
    steps n initial ≤ n * (2 * (initial + n) + 3) + 1 := by
  induction n generalizing initial with
  | zero => simp [steps]
  | succ n ih =>
      have hcost := incrementCost_le initial.bits
      have hsize := size_le_self initial
      have hnext := ih (initial + 1)
      rw [Nat.size_eq_bits_len] at hcost
      simp only [steps]
      nlinarith

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

inductive Label
  | scan | carry | restore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .carry, .restore]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {K Λ A : Type} [DecidableEq K]

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => (state.1, none))
    (match exit with | none => .halt | some label => .goto fun _ => label)

def instruction (source output scratch : K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .scan => .pop source (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (finish (some (labels .carry))) (finish exit))
  | .carry => .pop output (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.push scratch (fun _ => false) (finish (some (labels .carry))))
        (.push output (fun _ => true) (finish (some (labels .restore)))))
  | .restore => loopAt scratch output id false (labels .restore)
      (some (labels .scan))

def tapes (source output scratch : K) (base : K → List Bool)
    (input binary work : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base source input) output binary) scratch work

variable (source output scratch : K)
variable (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)

include hSO hSC in
@[simp] theorem tapes_source (base : K → List Bool) (input binary work : List Bool) :
    tapes source output scratch base input binary work source = input := by
  simp [tapes, hSO, hSC]

include hOC in
@[simp] theorem tapes_output (base : K → List Bool) (input binary work : List Bool) :
    tapes source output scratch base input binary work output = binary := by
  simp [tapes, hOC]

@[simp] theorem tapes_scratch (base : K → List Bool) (input binary work : List Bool) :
    tapes source output scratch base input binary work scratch = work := by
  simp [tapes]

theorem tapes_other (base : K → List Bool) (input binary work : List Bool) (k : K)
    (hks : k ≠ source) (hko : k ≠ output) (hkc : k ≠ scratch) :
    tapes source output scratch base input binary work k = base k := by
  simp [tapes, hks, hko, hkc]

include hSO hSC hOC in
private theorem update_source (base : K → List Bool) (input binary work next : List Bool) :
    Function.update (tapes source output scratch base input binary work) source next =
      tapes source output scratch base next binary work := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapes, hSO, hSC]
  · by_cases ho : k = output
    · subst k; simp [tapes, hs, hOC]
    · by_cases hc : k = scratch
      · subst k; simp [tapes, hs]
      · simp [tapes, hs, ho, hc]

include hOC in
private theorem update_output (base : K → List Bool) (input binary work next : List Bool) :
    Function.update (tapes source output scratch base input binary work) output next =
      tapes source output scratch base input next work := by
  funext k
  by_cases ho : k = output
  · subst k; simp [tapes, hOC]
  · by_cases hc : k = scratch
    · subst k; simp [tapes, ho]
    · simp [tapes, ho, hc]

private theorem update_scratch (base : K → List Bool) (input binary work next : List Bool) :
    Function.update (tapes source output scratch base input binary work) scratch next =
      tapes source output scratch base input binary next := by
  simp [tapes]

variable (labels : Label → Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
variable (base : K → List Bool) (ambient : A)

include hSO hSC hOC atLabels

theorem scanStep (bit : Bool) (input binary work : List Bool) :
    TM2.step program
      ⟨some (labels .scan), (ambient, none),
        tapes source output scratch base (bit :: input) binary work⟩ =
      some ⟨if bit then some (labels .carry) else exit, (ambient, none),
        tapes source output scratch base input binary work⟩ := by
  change some (TM2.stepAux (program (labels .scan)) _ _) = _
  rw [atLabels .scan]
  cases bit <;> cases exit <;>
    simp [instruction, finish, TM2.stepAux,
      tapes_source, hSO, hSC, hOC, update_source]

omit hSO hSC in
theorem carryStep_nil (input work : List Bool) :
    TM2.step program
      ⟨some (labels .carry), (ambient, none),
        tapes source output scratch base input [] work⟩ =
      some ⟨some (labels .restore), (ambient, none),
        tapes source output scratch base input [true] work⟩ := by
  change some (TM2.stepAux (program (labels .carry)) _ _) = _
  rw [atLabels .carry]
  simp [instruction, finish, TM2.stepAux, tapes_output, hOC, update_output]

omit hSO hSC in
theorem carryStep_false (input binary work : List Bool) :
    TM2.step program
      ⟨some (labels .carry), (ambient, none),
        tapes source output scratch base input (false :: binary) work⟩ =
      some ⟨some (labels .restore), (ambient, none),
        tapes source output scratch base input (true :: binary) work⟩ := by
  change some (TM2.stepAux (program (labels .carry)) _ _) = _
  rw [atLabels .carry]
  simp [instruction, finish, TM2.stepAux, tapes_output, hOC, update_output]

omit hSO hSC in
theorem carryStep_true (input binary work : List Bool) :
    TM2.step program
      ⟨some (labels .carry), (ambient, none),
        tapes source output scratch base input (true :: binary) work⟩ =
      some ⟨some (labels .carry), (ambient, none),
        tapes source output scratch base input binary (false :: work)⟩ := by
  change some (TM2.stepAux (program (labels .carry)) _ _) = _
  rw [atLabels .carry]
  simp [instruction, finish, TM2.stepAux, tapes_output, tapes_scratch,
    hOC, update_output, update_scratch]

omit hSO hSC in
theorem restoreTrace (input binary work : List Bool) :
    (advance (TM2.step program))^[work.length + 1]
      (some ⟨some (labels .restore), (ambient, none),
        tapes source output scratch base input binary work⟩) =
      some ⟨some (labels .scan), (ambient, none),
        tapes source output scratch base input (work.reverse ++ binary) []⟩ := by
  have h := transferAt_fromTapes (Γ := Alphabet (K := K)) scratch output hOC.symm
    id false (labels .restore) (some (labels .scan)) program (atLabels .restore)
    (tapes source output scratch base input binary work) ambient none
  have next_eq : nextAt output program = advance (TM2.step program) := by
    funext state
    rfl
  rw [next_eq] at h
  simpa only [tapes_scratch, tapes_output source output scratch hOC,
    List.map_id_fun, id_eq, tapesAt, update_scratch,
    update_output source output scratch hOC] using h

omit [DecidableEq K] hSO hSC hOC atLabels in
private theorem oneStepTrace {X : Type} {f : X → Option X} {a b : X}
    (h : f a = some b) : (advance f)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

omit [DecidableEq K] hSO hSC hOC atLabels in
private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

omit hSO hSC in
theorem incrementTrace (input binary work : List Bool) :
    (advance (TM2.step program))^[incrementCost binary + work.length]
      (some ⟨some (labels .carry), (ambient, none),
        tapes source output scratch base input binary work⟩) =
      some ⟨some (labels .scan), (ambient, none),
        tapes source output scratch base input (work.reverse ++ increment binary) []⟩ := by
  induction binary generalizing work with
  | nil =>
      have first := carryStep_nil source output scratch hOC
        labels exit program atLabels base ambient input work
      have second := restoreTrace source output scratch hOC
        labels exit program atLabels base ambient input [true] work
      have full := joinTrace (oneStepTrace first) second
      have clock : 1 + (work.length + 1) = 2 + work.length := by omega
      rw [clock] at full
      simpa only [incrementCost, increment] using full
  | cons bit binary ih =>
      cases bit with
      | false =>
          have first := carryStep_false source output scratch hOC
            labels exit program atLabels base ambient input binary work
          have second := restoreTrace source output scratch hOC
            labels exit program atLabels base ambient input (true :: binary) work
          have full := joinTrace (oneStepTrace first) second
          have clock : 1 + (work.length + 1) = 2 + work.length := by omega
          rw [clock] at full
          simpa only [incrementCost, increment] using full
      | true =>
          have first := carryStep_true source output scratch hOC
            labels exit program atLabels base ambient input binary work
          have second := ih (false :: work)
          have full := joinTrace (oneStepTrace first) second
          have clock : 1 + (incrementCost binary + (false :: work).length) =
              (incrementCost binary + 2) + work.length := by
            simp only [List.length_cons]
            omega
          rw [clock] at full
          simpa only [incrementCost, increment, List.reverse_cons,
            List.append_assoc, List.singleton_append] using full

theorem convertTrace (n initial : Nat) (suffix : List Bool) :
    (advance (TM2.step program))^[steps n initial]
      (some ⟨some (labels .scan), (ambient, none),
        tapes source output scratch base (encodeWord n ++ suffix) initial.bits []⟩) =
      some ⟨exit, (ambient, none),
        tapes source output scratch base suffix (initial + n).bits []⟩ := by
  induction n generalizing initial with
  | zero =>
      simpa only [steps, encodeWord, List.replicate_zero, List.nil_append,
        List.singleton_append, Nat.add_zero, Bool.false_eq_true, ↓reduceIte,
        Function.iterate_one, advance_some] using
        scanStep source output scratch hSO hSC hOC labels exit program atLabels base ambient
          false suffix initial.bits []
  | succ n ih =>
      have first := scanStep source output scratch hSO hSC hOC
        labels exit program atLabels base ambient true (encodeWord n ++ suffix) initial.bits []
      have second := incrementTrace source output scratch hOC
        labels exit program atLabels base ambient (encodeWord n ++ suffix) initial.bits []
      simp only [↓reduceIte] at first
      simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append,
        increment_bits] at second
      have third := ih (initial + 1)
      have full := joinTrace (joinTrace
        (oneStepTrace first) second) third
      simpa only [steps, encodeWord, List.replicate_succ, List.cons_append,
        Nat.add_assoc, Nat.add_comm 1 n] using full

def convertInTime (n initial : Nat) (suffix : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), (ambient, none),
        tapes source output scratch base (encodeWord n ++ suffix) initial.bits []⟩
      (some ⟨exit, (ambient, none),
        tapes source output scratch base suffix (initial + n).bits []⟩)
      (n * (2 * (initial + n) + 3) + 1) where
  steps := steps n initial
  evals_in_steps := convertTrace source output scratch hSO hSC hOC
    labels exit program atLabels base ambient n initial suffix
  steps_le_m := steps_le n initial

end BinPackingGap.UnaryToBinaryMachine

namespace BinPackingGap.BinaryAddMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinaryArithmetic

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := ((A × Bool) × Option Bool) × Option Bool

variable {A : Type}

def state (a : A) (carry : Bool) (left right : Option Bool) : State A :=
  (((a, carry), left), right)

def clean (a : A) : State A := state a false none none

variable {K Λ A : Type} [DecidableEq K]

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun s => clean s.1.1.1) (exitAt exit)

def addLoop (left right output : K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop left (fun s head => ((s.1.1, head), s.2))
    (.pop right (fun s head => (s.1, head))
      (.branch (fun s => s.1.2.isNone && s.2.isNone)
        (.branch (fun s => s.1.1.2)
          (.push output (fun _ => true) (finish exit)) (finish exit))
        (.push output (fun s => sumBit (s.1.2.getD false) (s.2.getD false) s.1.1.2)
          (.load (fun s => state s.1.1.1
            (carryBit (s.1.2.getD false) (s.2.getD false) s.1.1.2) none none)
            (.goto fun _ => again)))))

def tapes (left right output : K) (base : K → List Bool)
    (xs ys out : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base left xs) right ys) output out

variable (left right output : K)
variable (hLR : left ≠ right) (hLO : left ≠ output) (hRO : right ≠ output)

include hLR hLO in
@[simp] theorem tapes_left (base : K → List Bool) (xs ys out : List Bool) :
    tapes left right output base xs ys out left = xs := by
  simp [tapes, hLR, hLO]

include hRO in
@[simp] theorem tapes_right (base : K → List Bool) (xs ys out : List Bool) :
    tapes left right output base xs ys out right = ys := by
  simp [tapes, hRO]

@[simp] theorem tapes_output (base : K → List Bool) (xs ys out : List Bool) :
    tapes left right output base xs ys out output = out := by simp [tapes]

theorem tapes_other (base : K → List Bool) (xs ys out : List Bool) (k : K)
    (hl : k ≠ left) (hr : k ≠ right) (ho : k ≠ output) :
    tapes left right output base xs ys out k = base k := by
  simp [tapes, hl, hr, ho]

include hLR hLO hRO in
theorem update_left (base : K → List Bool) (xs ys out next : List Bool) :
    Function.update (tapes left right output base xs ys out) left next =
      tapes left right output base next ys out := by
  funext k
  by_cases hl : k = left
  · subst k; simp [tapes, hLR, hLO]
  · by_cases hr : k = right
    · subst k; simp [tapes, Ne.symm hLR, hRO]
    · by_cases ho : k = output
      · subst k; simp [tapes, Ne.symm hLO]
      · simp [tapes, hl, hr, ho]

include hRO in
theorem update_right (base : K → List Bool) (xs ys out next : List Bool) :
    Function.update (tapes left right output base xs ys out) right next =
      tapes left right output base xs next out := by
  funext k
  by_cases hr : k = right
  · subst k; simp [tapes, hRO]
  · by_cases ho : k = output
    · subst k; simp [tapes, Ne.symm hRO]
    · simp [tapes, hr, ho]

theorem update_output (base : K → List Bool) (xs ys out next : List Bool) :
    Function.update (tapes left right output base xs ys out) output next =
      tapes left right output base xs ys next := by
  simp [tapes]

variable (again : Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atAdd : program again = addLoop left right output again exit)
variable (base : K → List Bool) (ambient : A)

include hLR hLO hRO atAdd

theorem step_done (out : List Bool) (carry : Bool) (lreg rreg : Option Bool) :
    TM2.step program
      ⟨some again, state ambient carry lreg rreg, tapes left right output base [] [] out⟩ =
      some ⟨exit, clean ambient, tapes left right output base [] []
        (if carry then true :: out else out)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atAdd]
  cases carry <;> cases exit <;>
    simp [addLoop, finish, exitAt, clean, state, TM2.stepAux,
      hLR, hLO, hRO, tapes_left, tapes_right, update_left, update_right, update_output]

theorem step_more (xs ys out : List Bool) (carry : Bool) (lreg rreg : Option Bool)
    (more : xs ≠ [] ∨ ys ≠ []) :
    TM2.step program
      ⟨some again, state ambient carry lreg rreg, tapes left right output base xs ys out⟩ =
      some ⟨some again, state ambient
        (carryBit (xs.headD false) (ys.headD false) carry) none none,
        tapes left right output base xs.tail ys.tail
          (sumBit (xs.headD false) (ys.headD false) carry :: out)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atAdd]
  cases xs with
  | nil =>
      cases ys with
      | nil => simp at more
      | cons y ys =>
          simp [addLoop, state, TM2.stepAux, hLR, hLO, hRO,
            tapes_left, tapes_right, update_left, update_right, update_output]
  | cons x xs =>
      cases ys <;>
        simp [addLoop, state, TM2.stepAux, hLR, hLO, hRO,
          tapes_left, tapes_right, update_left, update_right, update_output]

theorem addTrace (xs ys out : List Bool) (carry : Bool) (lreg rreg : Option Bool) :
    (advance (TM2.step program))^[max xs.length ys.length + 1]
      (some ⟨some again, state ambient carry lreg rreg,
        tapes left right output base xs ys out⟩) =
      some ⟨exit, clean ambient,
        tapes left right output base [] [] ((addCarry xs ys carry).reverse ++ out)⟩ := by
  induction xs generalizing ys out carry lreg rreg with
  | nil =>
      induction ys generalizing out carry lreg rreg with
      | nil =>
          have run := step_done left right output hLR hLO hRO again exit program atAdd
            base ambient out carry lreg rreg
          cases carry <;> simpa [addCarry, List.length_nil, advance_some] using run
      | cons y ys ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply]
          simp only [advance_some]
          rw [step_more left right output hLR hLO hRO again exit program atAdd base ambient
            [] (y :: ys) out carry lreg rreg (Or.inr (List.cons_ne_nil _ _))]
          simpa [addCarry, List.reverse_cons, List.append_assoc] using
            ih (sumBit false y carry :: out) (carryBit false y carry) none none
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp only [List.length_cons, List.length_nil, Nat.max_zero]
          rw [Function.iterate_succ_apply]
          simp only [advance_some]
          rw [step_more left right output hLR hLO hRO again exit program atAdd base ambient
            (x :: xs) [] out carry lreg rreg (Or.inl (List.cons_ne_nil _ _))]
          simpa [addCarry, List.reverse_cons, List.append_assoc] using
            ih [] (sumBit x false carry :: out) (carryBit x false carry) none none
      | cons y ys =>
          rw [show max (x :: xs).length (y :: ys).length + 1 =
            (max xs.length ys.length + 1) + 1 by simp]
          rw [Function.iterate_succ_apply]
          simp only [advance_some]
          rw [step_more left right output hLR hLO hRO again exit program atAdd base ambient
            (x :: xs) (y :: ys) out carry lreg rreg (Or.inl (List.cons_ne_nil _ _))]
          simpa [addCarry, List.reverse_cons, List.append_assoc] using
            ih ys (sumBit x y carry :: out) (carryBit x y carry) none none

def addInTime (xs ys out : List Bool) (carry : Bool) (lreg rreg : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, state ambient carry lreg rreg, tapes left right output base xs ys out⟩
      (some ⟨exit, clean ambient,
        tapes left right output base [] [] ((addCarry xs ys carry).reverse ++ out)⟩)
      (max xs.length ys.length + 1) where
  steps := max xs.length ys.length + 1
  evals_in_steps := addTrace left right output hLR hLO hRO again exit program atAdd base ambient
    xs ys out carry lreg rreg
  steps_le_m := Nat.le_refl _

def addNatInTime (a b : Nat) (out : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, clean ambient, tapes left right output base a.bits b.bits out⟩
      (some ⟨exit, clean ambient,
        tapes left right output base [] [] ((a + b).bits.reverse ++ out)⟩)
      (max a.size b.size + 1) := by
  simpa [clean, addCarry_bits, Nat.size_eq_bits_len] using
    addInTime left right output hLR hLO hRO again exit program atAdd base ambient
      a.bits b.bits out false none none

end BinPackingGap.BinaryAddMachine

namespace BinPackingGap.BinaryTallyMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinaryAddMachine (State clean)

abbrev Label := UnaryToBinaryMachine.Label
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {K Λ A : Type} [DecidableEq K]

def instruction (source output scratch : K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  UnaryToBinaryMachine.instruction (A := (A × Bool) × Option Bool)
    source output scratch labels exit

theorem tallyTrace (source output scratch : K)
    (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
    (base : K → List Bool) (ambient : A) (n : ℕ) (suffix : List Bool) :
    (advance (TM2.step program))^[UnaryToBinaryMachine.steps n 0]
      (some ⟨some (labels .scan), clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base (encodeWord n ++ suffix) [] []⟩) =
      some ⟨exit, clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base suffix n.bits []⟩ := by
  simpa only [Nat.zero_bits, Nat.zero_add, BinaryAddMachine.clean, BinaryAddMachine.state] using
    UnaryToBinaryMachine.convertTrace source output scratch hSO hSC hOC
      labels exit program atLabels base ((ambient, false), none) n 0 suffix

theorem tally_steps_le (n : ℕ) :
    UnaryToBinaryMachine.steps n 0 ≤ 3 * (n + 1) ^ 2 := by
  have h := UnaryToBinaryMachine.steps_le n 0
  nlinarith

def tallyInTime (source output scratch : K)
    (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
    (base : K → List Bool) (ambient : A) (n : ℕ) (suffix : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base (encodeWord n ++ suffix) [] []⟩
      (some ⟨exit, clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base suffix n.bits []⟩)
      (3 * (n + 1) ^ 2) where
  steps := UnaryToBinaryMachine.steps n 0
  evals_in_steps := tallyTrace source output scratch hSO hSC hOC
    labels exit program atLabels base ambient n suffix
  steps_le_m := tally_steps_le n

private theorem joinPlainTrace {X : Type} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

private theorem stepAsPlainTrace {X : Type} {step : X → Option X} {a b : X}
    (h : step a = some b) : (advance step)^[1] (some a) = some b := h

theorem plainScanEmpty (source output scratch : K)
    (hSO : source ≠ output) (hSC : source ≠ scratch)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
    (base : K → List Bool) (ambient : A) (binary work : List Bool) :
    TM2.step program
      ⟨some (labels .scan), clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base [] binary work⟩ =
      some ⟨exit, clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base [] binary work⟩ := by
  let frame := UnaryToBinaryMachine.tapes source output scratch base [] binary work
  have hs : frame source = [] :=
    UnaryToBinaryMachine.tapes_source source output scratch hSO hSC base [] binary work
  have hu : Function.update frame source [] = frame := by
    rw [← hs, Function.update_eq_self]
  change some (TM2.stepAux (program (labels .scan)) (clean ambient) frame) = _
  rw [atLabels .scan]
  cases exit <;>
    simp [instruction, UnaryToBinaryMachine.instruction, UnaryToBinaryMachine.finish,
      TM2.stepAux, BinaryAddMachine.clean, BinaryAddMachine.state, hs, hu] <;> rfl

theorem plainConvertTrace (source output scratch : K)
    (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
    (base : K → List Bool) (ambient : A) (n initial : Nat) :
    (advance (TM2.step program))^[UnaryToBinaryMachine.steps n initial]
      (some ⟨some (labels .scan), clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base
          (List.replicate n true) initial.bits []⟩) =
      some ⟨exit, clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base [] (initial + n).bits []⟩ := by
  induction n generalizing initial with
  | zero =>
      simpa only [UnaryToBinaryMachine.steps, List.replicate_zero, Nat.add_zero,
        Function.iterate_one, advance_some] using
        plainScanEmpty source output scratch hSO hSC labels exit program atLabels
          base ambient initial.bits []
  | succ n ih =>
      have first := UnaryToBinaryMachine.scanStep source output scratch hSO hSC hOC
        labels exit program atLabels base ((ambient, false), none)
        true (List.replicate n true) initial.bits []
      have second := UnaryToBinaryMachine.incrementTrace source output scratch hOC
        labels exit program atLabels base ((ambient, false), none)
        (List.replicate n true) initial.bits []
      simp only [↓reduceIte] at first
      simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append,
        UnaryToBinaryMachine.increment_bits] at second
      have third := ih (initial + 1)
      have full := joinPlainTrace (joinPlainTrace (stepAsPlainTrace first) second) third
      simpa only [UnaryToBinaryMachine.steps, List.replicate_succ,
        BinaryAddMachine.clean, BinaryAddMachine.state,
        Nat.add_assoc, Nat.add_comm 1 n] using full

theorem plainTallyTrace (source output scratch : K)
    (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
    (base : K → List Bool) (ambient : A) (n : Nat) :
    (advance (TM2.step program))^[UnaryToBinaryMachine.steps n 0]
      (some ⟨some (labels .scan), clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base (List.replicate n true) [] []⟩) =
      some ⟨exit, clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base [] n.bits []⟩ := by
  simpa only [Nat.zero_bits, Nat.zero_add] using
    plainConvertTrace source output scratch hSO hSC hOC labels exit program atLabels
      base ambient n 0

def plainTallyInTime (source output scratch : K)
    (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
    (base : K → List Bool) (ambient : A) (n : Nat) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base (List.replicate n true) [] []⟩
      (some ⟨exit, clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base [] n.bits []⟩)
      (3 * (n + 1) ^ 2) where
  steps := UnaryToBinaryMachine.steps n 0
  evals_in_steps := plainTallyTrace source output scratch hSO hSC hOC
    labels exit program atLabels base ambient n
  steps_le_m := tally_steps_le n

def plainTallyFromTapesInTime (source output scratch : K)
    (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
    (base : K → List Bool) (ambient : A) (n : Nat)
    (sourceWord : base source = List.replicate n true)
    (outputEmpty : base output = []) (scratchEmpty : base scratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), clean ambient, base⟩
      (some ⟨exit, clean ambient, Function.update (Function.update base source []) output n.bits⟩)
      (3 * (n + 1) ^ 2) := by
  have hs : Function.update base source (List.replicate n true) = base := by
    rw [← sourceWord, Function.update_eq_self]
  have ho : Function.update base output [] = base := by
    rw [← outputEmpty, Function.update_eq_self]
  have hc : Function.update base scratch [] = base := by
    rw [← scratchEmpty, Function.update_eq_self]
  have hstart : UnaryToBinaryMachine.tapes source output scratch base
      (List.replicate n true) [] [] = base := by
    rw [UnaryToBinaryMachine.tapes, hs, ho, hc]
  have hfinish : UnaryToBinaryMachine.tapes source output scratch base [] n.bits [] =
      Function.update (Function.update base source []) output n.bits := by
    let done := Function.update (Function.update base source []) output n.bits
    have hwork : done scratch = [] := by
      simp [done, Ne.symm hSC, Ne.symm hOC, scratchEmpty]
    change Function.update done scratch [] = done
    rw [← hwork, Function.update_eq_self]
  have run := plainTallyInTime source output scratch hSO hSC hOC
    labels exit program atLabels base ambient n
  simpa only [hstart, hfinish] using run

theorem result_other (source output scratch : K) (base : K → List Bool)
    (suffix : List Bool) (n : ℕ) (k : K)
    (hs : k ≠ source) (ho : k ≠ output) (hc : k ≠ scratch) :
    UnaryToBinaryMachine.tapes source output scratch base suffix n.bits [] k = base k :=
  UnaryToBinaryMachine.tapes_other source output scratch base suffix n.bits [] k hs ho hc

def machine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label
  main := .scan
  σ := State Unit
  initialState := clean ()
  m := instruction 0 1 2 id none

def configuration (label : Option Label) (input output : List Bool) : machine.Cfg :=
  ⟨label, clean (), UnaryToBinaryMachine.tapes (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
    (fun _ => []) input output []⟩

theorem initList_eq (input : List Bool) :
    initList machine input = configuration (some .scan) input [] := by
  unfold initList configuration machine
  congr 1
  funext k
  fin_cases k <;> simp [UnaryToBinaryMachine.tapes]

theorem haltList_eq (output : List Bool) :
    haltList machine output = configuration none [] output := by
  unfold haltList configuration machine
  congr 1
  funext k
  fin_cases k <;> simp [UnaryToBinaryMachine.tapes]

theorem machineTrace (n : ℕ) :
    (advance machine.step)^[UnaryToBinaryMachine.steps n 0]
      (some (initList machine (encodeWord n))) =
      some (haltList machine n.bits) := by
  rw [initList_eq, haltList_eq]
  have h := tallyTrace (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    id none machine.m (fun _ => rfl) (fun _ => []) () n []
  simpa only [List.append_nil, configuration, id_eq, FinTM2.step, FinTM2.Cfg,
    machine, Alphabet] using! h

def outputsInTime (n : ℕ) :
    TM2OutputsInTime machine (encodeWord n) (some n.bits) (3 * (n + 1) ^ 2) where
  steps := UnaryToBinaryMachine.steps n 0
  evals_in_steps := machineTrace n
  steps_le_m := tally_steps_le n

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeWord Nat.bits (id : ℕ → ℕ) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3 * Polynomial.X ^ 2
  outputsFun n := by
    change TM2OutputsInTime machine ((encodeWord n).map id)
      (some (n.bits.map id))
      ((Polynomial.C 3 * Polynomial.X ^ 2 : Polynomial ℕ).eval (encodeWord n).length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, encodeWord, List.length_append,
      List.length_replicate, List.length_singleton] using! outputsInTime n

theorem machine_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet machine := by
  intro tape
  change Finite Bool
  infer_instance

end BinPackingGap.BinaryTallyMachine

end OAI
