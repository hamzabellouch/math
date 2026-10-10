import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.GCDMachineRun

namespace OAI

section

namespace KS.W30.GCDMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

def outputState (g : List Bool) : Fin 10 → List Bool :=
  DivisionMachine.«stacks» [] [] g [] [] [] [] []

theorem finish_spec (g : List Bool) :
    RunSpec finish (state g []) (outputState g) (g.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_move_stacks (3 : Fin 10) 5 (by decide)
    (state g []) bits (by
      change bits.length=g.reverse.length+1
      simpa only [List.length_reverse] using hlen)
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (3 : Fin 10) 5) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [state,outputState,DivisionMachine.«stacks»,
      KS.W04.BinaryStackMoves.twoConfig]

lemma gcd_encode_length_le (x y : List Bool) (L : ℕ)
    (hx : x.length ≤ L) (hy : y.length ≤ L) :
    (Computability.encodeNat (Nat.gcd (bitsValue x) (bitsValue y))).length ≤ L := by
  by_cases hz : bitsValue y = 0
  · rw [hz, Nat.gcd_zero_right, encodeNat_length_eq_size]
    exact (Nat.size_le.mpr (bitsValue_lt_two_pow_length x)).trans hx
  · have h := (KS.W30.BinaryGCD.gcdBits_length_le_right x y (Nat.pos_of_ne_zero hz)).trans hy
    simpa only [KS.W30.BinaryGCD.gcdBits_eq_encodeNat] using h

theorem program_spec (x y : List Bool) (L : ℕ)
    (hxc : CanonicalBits x) (hyc : CanonicalBits y)
    (hx : x.length ≤ L) (hy : y.length ≤ L) :
    RunSpec program (state x y)
      (outputState (Computability.encodeNat (Nat.gcd (bitsValue x) (bitsValue y))))
      (100 * (L + 1) ^ 3) := by
  let g := Computability.encodeNat (Nat.gcd (bitsValue x) (bitsValue y))
  have hloop : RunSpec loop (state x y) (state g [])
      ((2 * y.length + 1) * (40 * (L + 1) ^ 2 + 1)) := by
    intro bits hlen
    exact loop_run y.length x y bits L hxc hyc hx hy
      (bitsValue_lt_two_pow_length y) (by omega)
  have hf := finish_spec g
  have h := hloop.compose hf
  have hg : g.length ≤ L := gcd_encode_length_le x y L hx hy
  have hb : (2 * y.length + 1) * (40 * (L + 1) ^ 2 + 1) ≤
      (2 * L + 1) * (40 * (L + 1) ^ 2 + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (L + 1)
  have hquad : 1 ≤ (L + 1) ^ 2 := by
    have hp : 0 < (L + 1) ^ 2 := Nat.pow_pos (by omega)
    omega
  have hpoly : (2 * L + 1) * (40 * (L + 1) ^ 2 + 1) ≤ 82 * (L + 1) ^ 3 := by
    calc
      _ ≤ (2 * (L + 1)) * (41 * (L + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have ht : (2 * y.length + 1) * (40 * (L + 1) ^ 2 + 1) + (g.length + 1) ≤
      100 * (L + 1) ^ 3 := by omega
  exact h.mono ht

theorem canonical_gcd_machine (a b : ℕ) :
    RunSpec program
      (state (Computability.encodeNat a) (Computability.encodeNat b))
      (outputState (Computability.encodeNat (Nat.gcd a b)))
      (100 * (Nat.size a + Nat.size b + 1) ^ 3) := by
  have h := program_spec (Computability.encodeNat a) (Computability.encodeNat b)
    (Nat.size a + Nat.size b) (canonicalBits_encodeNat _) (canonicalBits_encodeNat _)
    (by simp only [encodeNat_length_eq_size]; omega)
    (by simp only [encodeNat_length_eq_size]; omega)
  simpa only [bitsValue_encodeNat] using h

end KS.W30.GCDMachine

end

end OAI
