import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MediatorProgram
import OAI.Computability.QuantumFactoring.BitStackListFold

namespace OAI

/-! Actual polynomial rational-list summation. Unreduced numerator and
positive denominator registers are accumulated with ordinary integer
arithmetic, then reduced once. Their bit lengths grow cubically at most. -/

namespace ContinuumCoulomb.RationalSumProgram
open ExactQuantumFactoring.BitStackProgram
open scoped BigOperators

abbrev State := ℤ × ℕ

def stateCode : State → List Bool := prodCode intCode Nat.bits

def step (s : State) (q : ℚ) : State :=
  (s.1 * q.den + q.num * s.2, s.2 * q.den)

def value (s : State) : ℚ := (s.1 : ℚ) / s.2

theorem step_den_pos (s : State) (q : ℚ) (hs : 0 < s.2) : 0 < (step s q).2 :=
  Nat.mul_pos hs q.pos

theorem step_value (s : State) (q : ℚ) (hs : 0 < s.2) : value (step s q) = value s + q := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hs' : (s.2 : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold step value
  push_cast
  conv_rhs => rw [← Rat.num_div_den q]
  field_simp

theorem fold_den_pos (xs : List ℚ) (s : State) (hs : 0 < s.2) :
    0 < (xs.foldl step s).2 := by
  induction xs generalizing s with
  | nil => exact hs
  | cons q xs ih => exact ih _ (step_den_pos s q hs)

theorem fold_value (xs : List ℚ) (s : State) (hs : 0 < s.2) :
    value (xs.foldl step s) = value s + xs.sum := by
  induction xs generalizing s with
  | nil => simp
  | cons q xs ih =>
    rw [List.foldl_cons, ih _ (step_den_pos s q hs), step_value s q hs, List.sum_cons]
    ring

theorem integer_bits_add (a b : ℤ) :
    (a + b).natAbs.bits.length ≤ a.natAbs.bits.length + b.natAbs.bits.length + 1 :=
  (bits_length_mono (Int.natAbs_add_le a b)).trans (bits_length_add _ _)

theorem step_bits (s : State) (q : ℚ) :
    (step s q).2.bits.length ≤ s.2.bits.length + q.den.bits.length ∧
    (step s q).1.natAbs.bits.length ≤ s.1.natAbs.bits.length + q.den.bits.length +
      q.num.natAbs.bits.length + s.2.bits.length + 1 := by
  constructor
  · exact bits_length_mul _ _
  · have h := integer_bits_add (s.1 * q.den) (q.num * s.2)
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at h
    have h1 := bits_length_mul s.1.natAbs q.den
    have h2 := bits_length_mul q.num.natAbs s.2
    exact h.trans (by omega)

theorem fold_bits (xs : List ℚ) (s : State) (B : ℕ)
    (hB : ∀ q ∈ xs, q.num.natAbs.bits.length + q.den.bits.length ≤ B) :
    (xs.foldl step s).2.bits.length ≤ s.2.bits.length + xs.length * B ∧
    (xs.foldl step s).1.natAbs.bits.length ≤ s.1.natAbs.bits.length +
      xs.length * (B + s.2.bits.length + xs.length * B + 1) := by
  induction xs generalizing s with
  | nil => simp
  | cons q xs ih =>
    have hq := hB q (by simp)
    have hi := ih (step s q) (by intro a ha; exact hB a (by simp [ha]))
    have hs := step_bits s q
    simp only [List.foldl_cons, List.length_cons]
    constructor
    · nlinarith [hi.1]
    · nlinarith [hi.2]

theorem state_length (s : State) :
    (stateCode s).length = 2 * s.1.natAbs.bits.length + s.2.bits.length + 7 := by
  simp only [stateCode, prodCode, intCode, intData, pairBits_length, Procedure.boolCode,
    List.length_singleton]
  omega

theorem rational_length (q : ℚ) :
    (ratCode q).length = 2 * q.num.natAbs.bits.length + q.den.bits.length + 7 :=
  state_length (q.num, q.den)

noncomputable def stepProgram : Procedure (prodCode ratCode stateCode) stateCode
    (fun x => step x.2 x.1) := by
  let q := Procedure.first ratCode stateCode
  let s := Procedure.second ratCode stateCode
  let qn := Procedure.ratNum.comp q
  let qd := Procedure.ratDen.comp q
  let sn := (Procedure.first intCode Nat.bits).comp s
  let sd := (Procedure.second intCode Nat.bits).comp s
  let first := Procedure.intMul.comp (sn.pair (Procedure.natToInt.comp qd))
  let second := Procedure.intMul.comp (qn.pair (Procedure.natToInt.comp sd))
  exact ((Procedure.intAdd.comp (first.pair second)).pair
    (Procedure.binaryMul.comp (sd.pair qd))).congrFun (by intro x; rfl)

noncomputable def foldProgram : Procedure (prodCode (listCode ratCode) stateCode) stateCode
    (fun x => x.1.foldl step x.2) :=
  Procedure.foldList 0 stepProgram (Polynomial.C 20 * (Polynomial.X + 1) ^ 3) (by
    intro xs s i
    let L := (listCode ratCode xs).length + (stateCode s).length
    have hq : ∀ q ∈ xs.take i, q.num.natAbs.bits.length + q.den.bits.length ≤ L := by
      intro q hq
      have h := code_le_of_mem ratCode (List.mem_of_mem_take hq)
      rw [rational_length] at h
      dsimp only [L]
      omega
    have h := fold_bits (xs.take i) s L hq
    have hs := state_length s
    have hi : (xs.take i).length ≤ L :=
      (show (xs.take i).length ≤ xs.length by simp only [List.length_take]; omega).trans
        ((list_length_le_code ratCode xs).trans (Nat.le_add_right _ _))
    rw [state_length]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    change _ ≤ 20 * (L + 1) ^ 3
    have hs1 : s.1.natAbs.bits.length ≤ L := by dsimp only [L]; omega
    have hs2 : s.2.bits.length ≤ L := by dsimp only [L]; omega
    have hmul : (xs.take i).length * L ≤ L * L := Nat.mul_le_mul_right L hi
    have hn : (xs.take i).length * (L + s.2.bits.length + (xs.take i).length * L + 1) ≤
        L * (2 * L + L * L + 1) :=
      Nat.mul_le_mul hi (by omega)
    nlinarith [h.1, h.2])

noncomputable def sumProgram : Procedure (listCode ratCode) ratCode List.sum := by
  let start := (Procedure.identity (listCode ratCode)).pair
    (Procedure.constant (listCode ratCode) stateCode (0, 1))
  exact (Procedure.makeRat.comp (foldProgram.comp start)).congrFun (by
    intro xs
    change mkRat (xs.foldl step (0, 1)).1 (xs.foldl step (0, 1)).2 = xs.sum
    rw [Rat.mkRat_eq_div]
    have h := fold_value xs (0, 1) (by norm_num)
    simpa only [value, Int.cast_zero, Nat.cast_one, zero_div, zero_add] using h)

end ContinuumCoulomb.RationalSumProgram

end OAI
