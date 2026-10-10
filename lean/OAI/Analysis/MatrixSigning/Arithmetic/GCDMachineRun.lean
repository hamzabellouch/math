import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.GCDMachineStep

namespace OAI

section

namespace KS.W30.GCDMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19 KS.W30.BinaryGCD

theorem loop_advance (x y bits : List Bool) (L : ℕ)
    (hx : x.length ≤ L) (hy : y.length ≤ L) (hyp : 0 < bitsValue y)
    (hlen : 40 * (L + 1) ^ 2 + 1 ≤ bits.length) :
    ∃ rest : List Bool, bits.length - (40 * (L + 1) ^ 2 + 1) ≤ rest.length ∧
      loop.toMachine.run ⟨some loop.initial, state x y⟩ bits =
        loop.toMachine.run ⟨some loop.initial, state y (trimBits (divideBits y x).2)⟩ rest := by
  cases bits with
  | nil => simp at hlen
  | cons coin tail =>
    have hne : y ≠ [] := by intro h; simp [h, bitsValue] at hyp
    have ht : 40 * (L + 1) ^ 2 ≤ tail.length := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨rest, hrest, he⟩ := (body_spec x y L hx hy hyp).loop_body_then guard tail ht
    refine ⟨rest, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · rw [Machine.run, guard_nonzero x y hne coin]
      exact he

lemma loop_zero (x bits : List Bool) (hlen : 1 ≤ bits.length) :
    loop.toMachine.run ⟨some loop.initial, state x []⟩ bits = ⟨none, state x []⟩ := by
  cases bits with
  | nil => simp at hlen
  | cons coin tail => rw [Machine.run, guard_zero, Machine.run_halted _ _ rfl]

lemma canonical_eq_encode (xs : List Bool) (h : CanonicalBits xs) :
    xs = Computability.encodeNat (bitsValue xs) := by
  apply canonicalBits_injective h (canonicalBits_encodeNat _)
  rw [bitsValue_encodeNat]

theorem loop_run (k : ℕ) (x y bits : List Bool) (L : ℕ)
    (hxc : CanonicalBits x) (hyc : CanonicalBits y)
    (hx : x.length ≤ L) (hy : y.length ≤ L) (hyb : bitsValue y < 2 ^ k)
    (hlen : (2 * k + 1) * (40 * (L + 1) ^ 2 + 1) ≤ bits.length) :
    loop.toMachine.run ⟨some loop.initial, state x y⟩ bits =
      ⟨none, state (Computability.encodeNat (Nat.gcd (bitsValue x) (bitsValue y))) []⟩ := by
  induction k generalizing x y bits with
  | zero =>
    have hyv : bitsValue y = 0 := by simpa using hyb
    have hy0 : y = [] := by
      apply canonicalBits_injective hyc (by simp [CanonicalBits])
      simpa only [bitsValue] using hyv
    subst y
    have hh : 1 ≤ bits.length := by
      simp only [Nat.mul_zero, Nat.zero_add, Nat.one_mul] at hlen
      omega
    rw [loop_zero x bits hh]
    simp only [bitsValue, Nat.gcd_zero_right, ← canonical_eq_encode x hxc]
  | succ k ih =>
    by_cases hy0 : y = []
    · subst y
      have hpos : 1 ≤ (2 * (k + 1) + 1) * (40 * (L + 1) ^ 2 + 1) := by
        have hp : 0 < (2 * (k + 1) + 1) * (40 * (L + 1) ^ 2 + 1) :=
          Nat.mul_pos (by omega) (by omega)
        omega
      rw [loop_zero x bits (hpos.trans hlen)]
      simp only [bitsValue, Nat.gcd_zero_right, ← canonical_eq_encode x hxc]
    · have hyp : 0 < bitsValue y := canonicalBits_value_pos y hyc hy0
      let T := 40 * (L + 1) ^ 2 + 1
      have hbudget : (2 * (k + 1) + 1) * T = 2 * T + (2 * k + 1) * T := by ring
      have hlen' : 2 * T + (2 * k + 1) * T ≤ bits.length := by
        change (2 * (k + 1) + 1) * T ≤ bits.length at hlen
        rwa [hbudget] at hlen
      have hT : 1 ≤ T := by dsimp [T]; omega
      obtain ⟨rest, hrest, hstep⟩ := loop_advance x y bits L hx hy hyp (by dsimp [T] at *; omega)
      let r := trimBits (divideBits y x).2
      have hrlen : r.length ≤ L := (trimmed_remainder_length_le y x hyp).trans hy
      have hrc : CanonicalBits r := trimBits_canonical _
      have hrv : bitsValue r = bitsValue x % bitsValue y := by
        dsimp only [r]
        rw [trimBits_value, remainder_value y x hyp]
      have hrest' : T + (2 * k + 1) * T ≤ rest.length := by
        change bits.length - T ≤ rest.length at hrest
        omega
      rw [hstep]
      change loop.toMachine.run ⟨some loop.initial, state y r⟩ rest = _
      by_cases hr0 : r = []
      · have hm : bitsValue x % bitsValue y = 0 := by simpa [hr0, bitsValue] using hrv.symm
        have hg : Nat.gcd (bitsValue x) (bitsValue y) = bitsValue y := by
          rw [Nat.gcd_comm, Nat.gcd_rec, hm, Nat.gcd_zero_left]
        rw [hr0, loop_zero y rest (by omega), hg, ← canonical_eq_encode y hyc]
      · have hrp : 0 < bitsValue r := canonicalBits_value_pos r hrc hr0
        obtain ⟨last, hlast, hstep'⟩ := loop_advance y r rest L hy hrlen hrp (by change T ≤ rest.length; omega)
        let s := trimBits (divideBits r y).2
        have hslen : s.length ≤ L := (trimmed_remainder_length_le r y hrp).trans hrlen
        have hsc : CanonicalBits s := trimBits_canonical _
        have hsv : bitsValue s = bitsValue y % bitsValue r := by
          dsimp only [s]
          rw [trimBits_value, remainder_value r y hrp]
        have hsb : bitsValue s < 2 ^ k := by
          rw [hsv]
          have hrb : bitsValue r < bitsValue y := by rw [hrv]; exact Nat.mod_lt _ hyp
          exact remainder_below_half hrp hrb (by simpa [pow_succ, Nat.mul_comm] using hyb)
        have hlast' : (2 * k + 1) * (40 * (L + 1) ^ 2 + 1) ≤ last.length := by
          change rest.length - T ≤ last.length at hlast
          change (2 * k + 1) * T ≤ last.length
          omega
        rw [hstep']
        have hi := ih r s last hrc hsc hrlen hslen hsb hlast'
        change loop.toMachine.run ⟨some loop.initial, state r s⟩ last = _
        rw [hi]
        have hg : Nat.gcd (bitsValue x) (bitsValue y) = Nat.gcd (bitsValue r) (bitsValue s) := by
          rw [hsv, hrv]
          exact gcd_two_reductions _ _
        rw [hg]

end KS.W30.GCDMachine

end

end OAI
