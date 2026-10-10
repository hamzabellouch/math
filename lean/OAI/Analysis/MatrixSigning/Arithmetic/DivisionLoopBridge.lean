import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.DivisionLoopModel
import OAI.Analysis.MatrixSigning.Arithmetic.DivisionCompatibility

namespace OAI

section

namespace KS.W30.BinaryRational
open KS.W19

theorem divisionLoop_canonical_outputs (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    normalizeDivisionPair (DivisionLoop.process divisor xs.reverse [] []) =
      normalizeDivisionPair (divideBits divisor xs) := by
  have h := DivisionLoop.process_payload_correct divisor xs hd
  exact normalizeDivisionPair_eq_divideBits divisor xs _ hd h.1 h.2

@[simp] theorem divisionLoop_trim_quotient (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    trimBits (DivisionLoop.process divisor xs.reverse [] []).1 =
      trimBits (divideBits divisor xs).1 :=
  congrArg Prod.fst (divisionLoop_canonical_outputs divisor xs hd)

@[simp] theorem divisionLoop_trim_remainder (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    trimBits (DivisionLoop.process divisor xs.reverse [] []).2 =
      trimBits (divideBits divisor xs).2 :=
  congrArg Prod.snd (divisionLoop_canonical_outputs divisor xs hd)

end KS.W30.BinaryRational

end

end OAI
