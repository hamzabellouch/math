import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.SignedRationalSerializer
import OAI.Analysis.MatrixSigning.Arithmetic.RationalReciprocalCore
import OAI.Analysis.MatrixSigning.Encoding.InverseEncodingSize

namespace OAI

section

namespace KS.W30.RationalReciprocal
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19
open KS.W03.MachineCombinators

def serializeCore : Program 13 := compose core KS.W01.SignedRationalSerializer.program

theorem serializeCore_spec (q : ℚ) :
    RunSpec serializeCore (canonicalState q)
      (KS.W01.SignedRationalSerializer.outputState (KS.W01.encodeRat q⁻¹))
      (600 * (KS.W01.ratLength q + 1) ^ 3) := by
  have hs := KS.W01.SignedRationalSerializer.serializes_rational q⁻¹
  have h := (core_spec q).compose hs
  have hp := KS.W01.rational_parts_size_le_length q⁻¹
  have hi := KS.W01.ratLength_inv_le q
  have hnum : (Computability.encodeNat (q⁻¹).num.natAbs).length ≤ 4 * KS.W01.ratLength q + 7 := by
    rw [encodeNat_length_eq_size]
    exact hp.1.trans hi
  have hden : (Computability.encodeNat (q⁻¹).den).length ≤ 4 * KS.W01.ratLength q + 7 := by
    rw [encodeNat_length_eq_size]
    exact hp.2.trans hi
  have hserial : 16 * ((Computability.encodeNat (q⁻¹).num.natAbs).length +
      (Computability.encodeNat (q⁻¹).den).length + 1) ≤ 240 * (KS.W01.ratLength q + 1) := by omega
  have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (KS.W01.ratLength q + 1)
  have ht : 310 * (KS.W01.ratLength q + 1) ^ 3 +
      16 * ((Computability.encodeNat (q⁻¹).num.natAbs).length +
        (Computability.encodeNat (q⁻¹).den).length + 1) ≤
      600 * (KS.W01.ratLength q + 1) ^ 3 := by omega
  exact h.mono ht

end KS.W30.RationalReciprocal

end

end OAI
