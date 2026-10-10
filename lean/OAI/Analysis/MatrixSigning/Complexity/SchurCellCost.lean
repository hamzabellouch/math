import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SchurCellMachine

namespace OAI

section

namespace KS.W07.SchurCellMachine

open KS.W01

def cellBudget (B : ℕ) : ℕ := 4000000 * (16 * B + 40) ^ 3

theorem ticks_le_cellBudget (x a b c : ℚ) (B : ℕ)
    (hx : x.num.natAbs ≤ 2 ^ B ∧ x.den ≤ 2 ^ B)
    (ha : a.num.natAbs ≤ 2 ^ B ∧ a.den ≤ 2 ^ B)
    (hb : b.num.natAbs ≤ 2 ^ B ∧ b.den ≤ 2 ^ B)
    (hc : c.num.natAbs ≤ 2 ^ B ∧ c.den ≤ 2 ^ B) :
    ticks x a b c ≤ cellBudget B := by
  have lx := ratLength_le_of_parts x B B hx.1 hx.2
  have la := ratLength_le_of_parts a B B ha.1 ha.2
  have lb := ratLength_le_of_parts b B B hb.1 hb.2
  have lc := ratLength_le_of_parts c B B hc.1 hc.2
  have hp := KS.W30.mul_parts_le_two_pow a b B B ha.1 ha.2 hb.1 hb.2
  have lp := ratLength_le_of_parts (a*b) (B+B) (B+B) hp.1 hp.2
  have hq := KS.W30.div_parts_le_two_pow (a*b) c (B+B) B hp.1 hp.2 hc.1 hc.2
  have lq := ratLength_le_of_parts (a*b/c) (B+B+B) (B+B+B) hq.1 hq.2
  let H := 16 * B + 40
  have hab : (KS.W15.RationalMultiply.inputBits a b).length + 1 ≤ H := by
    simp only [KS.W15.RationalMultiply.inputBits,List.length_append]
    change ratLength a + ratLength b + 1 ≤ H
    dsimp [H]; omega
  have hpc : (KS.W30.RationalDivision.inputBits (a*b) c).length + 1 ≤ H := by
    simp only [KS.W30.RationalDivision.inputBits,List.length_append]
    change ratLength (a*b) + ratLength c + 1 ≤ H
    dsimp [H]; omega
  have hxq : (encodeRat x ++ encodeRat (a*b/c)).length + 1 ≤ H := by
    rw [List.length_append]
    change ratLength x + ratLength (a*b/c) + 1 ≤ H
    dsimp [H]; omega
  have hm := (KS.W15.RationalMultiply.totalTicks_le_polynomial a b).trans
    (Nat.mul_le_mul_left 2048 (Nat.pow_le_pow_left hab 3))
  have hd := Nat.mul_le_mul_left 1100000 (Nat.pow_le_pow_left hpc 3)
  have hs := Nat.mul_le_mul_left 600000 (Nat.pow_le_pow_left hxq 3)
  have hH : H ≤ H^3 := Nat.le_self_pow (by decide : 3 ≠ 0) H
  unfold ticks cellBudget
  change _ ≤ 4000000 * H^3
  dsimp [KS.W29.polynomialFuel] at hm ⊢
  have htransfer : (4*ratLength a+2*ratLength b+4) +
      (4*ratLength (a*b)+2*ratLength c+4) +
      (4*ratLength x+2*ratLength (a*b/c)+4) ≤ 10*H := by
    dsimp [H]; omega
  omega

theorem polynomial_spec (x a b c : ℚ) (B : ℕ)
    (hx : x.num.natAbs ≤ 2 ^ B ∧ x.den ≤ 2 ^ B)
    (ha : a.num.natAbs ≤ 2 ^ B ∧ a.den ≤ 2 ^ B)
    (hb : b.num.natAbs ≤ 2 ^ B ∧ b.den ≤ 2 ^ B)
    (hc : c.num.natAbs ≤ 2 ^ B ∧ c.den ≤ 2 ^ B) :
    KS.W03.MachineCombinators.RunSpec program
      (workspace [] [] (encodeRat x) (encodeRat a) (encodeRat b) (encodeRat c))
      (workspace [] (encodeRat (x-a*b/c)) [] [] [] []) (cellBudget B) :=
  (full_spec x a b c).mono (ticks_le_cellBudget x a b c B hx ha hb hc)

end KS.W07.SchurCellMachine

end

end OAI
