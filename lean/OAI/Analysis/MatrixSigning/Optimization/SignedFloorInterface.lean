import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SignedFloorMachine

namespace OAI

section

namespace KS.W19.SignedFloorMachine
open KS.W03.MachineCombinators

def rationalRemainder (q : Rat) : List Bool :=
  (EncodedDivision.resultPair (Computability.encodeNat (KS.W01.intPayload q.num))
    (Computability.encodeNat q.den)).2

theorem rational_runSpec (q : Rat) :
    RunSpec program («stacks» (KS.W01.encodeRat q) [] [] [] [])
      («stacks» [] (Computability.encodeNat q.den) (KS.W01.encodeInt ⌊q⌋)
        (rationalRemainder q) [])
      (KS.W29.polynomialFuel 32 2 (KS.W01.encodeRat q).length) := by
  have h := (program_spec (negativeOfInt q.num)
    (Computability.encodeNat (KS.W01.intPayload q.num))
    (Computability.encodeNat q.den)).mono
      (fuel_quadratic (negativeOfInt q.num)
        (Computability.encodeNat (KS.W01.intPayload q.num))
        (Computability.encodeNat q.den))
  have hin : negativeOfInt q.num ::
      (KS.W01.frame (Computability.encodeNat (KS.W01.intPayload q.num)) ++
        KS.W01.frame (Computability.encodeNat q.den)) = KS.W01.encodeRat q :=
    (SignedFloor.encodeRat_constructor q).symm
  have hout : negativeOfInt q.num :: KS.W01.encodeNat
      (bitsValue (EncodedDivision.resultPair
        (Computability.encodeNat (KS.W01.intPayload q.num))
        (Computability.encodeNat q.den)).1) = KS.W01.encodeInt ⌊q⌋ :=
    SignedFloor.floor_wire q
  rw [hin, hout] at h
  exact h

end KS.W19.SignedFloorMachine

end

end OAI
