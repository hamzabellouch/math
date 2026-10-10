import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryDivision
import OAI.Analysis.MatrixSigning.Machines.DirectedRounding

namespace OAI

section

namespace KS.W19

def floorViaBinaryDivision (x : ℚ) : ℤ :=
  signedBitsValue (negativeOfInt x.num)
    (divideSignedBits (negativeOfInt x.num) (Computability.encodeNat x.den)
      (Computability.encodeNat (KS.W01.intPayload x.num))).1

theorem floorViaBinaryDivision_eq_floor (x : ℚ) : floorViaBinaryDivision x = ⌊x⌋ := by
  unfold floorViaBinaryDivision
  rw [divideSignedBits_intPayload_quotient x.num x.den x.den_pos, Rat.floor_def']

theorem directedRound_binary_floor (q z d : ℚ) :
    directedRound q z d = q * (floorViaBinaryDivision ((z - |d|) / q) : ℤ) := by
  rw [floorViaBinaryDivision_eq_floor]
  rfl

theorem floorViaBinaryDivision_core_cost (x : ℚ) :
    signedDivisionBitCost (negativeOfInt x.num) (Computability.encodeNat x.den)
      (Computability.encodeNat (KS.W01.intPayload x.num)) ≤
        6 * ((KS.W01.encodeRat x).length + 1) ^ 2 := by
  have h := signedDivisionBitCost_quadratic (negativeOfInt x.num)
    (Computability.encodeNat x.den) (Computability.encodeNat (KS.W01.intPayload x.num))
  rw [KS.W01.length_encodeRat]
  change signedDivisionBitCost _ _ _ ≤
    6 * ((2 * (KS.W01.natPayloadLength (KS.W01.intPayload x.num) +
      KS.W01.natPayloadLength x.den) + 3) + 1) ^ 2
  change signedDivisionBitCost _ _ _ ≤
    6 * (KS.W01.natPayloadLength (KS.W01.intPayload x.num) +
      KS.W01.natPayloadLength x.den + 1) ^ 2 at h
  exact h.trans (Nat.mul_le_mul_left 6 (Nat.pow_le_pow_left (by omega) 2))

end KS.W19

end

end OAI
