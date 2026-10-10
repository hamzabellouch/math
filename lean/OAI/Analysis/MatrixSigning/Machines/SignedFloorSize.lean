import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SignedFloorModel

namespace OAI

section

namespace KS.W19.SignedFloor

theorem floor_encodeInt_length_le_num (q : Rat) :
    (KS.W01.encodeInt ⌊q⌋).length ≤ (KS.W01.encodeInt q.num).length := by
  let raw := (DivisionLoop.process (Computability.encodeNat q.den)
    (Computability.encodeNat (KS.W01.intPayload q.num)).reverse [] []).1
  have hraw : raw.length = (Computability.encodeNat (KS.W01.intPayload q.num)).length := by
    simpa only [List.length_nil, List.length_reverse, Nat.zero_add] using
      DivisionLoop.process_quotient_length (Computability.encodeNat q.den)
        (Computability.encodeNat (KS.W01.intPayload q.num)).reverse [] []
  have hcan : (Computability.encodeNat (bitsValue raw)).length ≤ raw.length := by
    rw [← trimBits_eq_encodeNat]
    exact trimBits_length_le raw
  rw [← floor_wire, List.length_cons, KS.W01.length_encodeNat, KS.W01.length_encodeInt]
  change (2 * (Computability.encodeNat (bitsValue raw)).length + 1) + 1 ≤
    2 * (Computability.encodeNat (KS.W01.intPayload q.num)).length + 2
  omega

theorem floor_encodeInt_length_le_input (q : Rat) :
    (KS.W01.encodeInt ⌊q⌋).length ≤ (KS.W01.encodeRat q).length := by
  have h := floor_encodeInt_length_le_num q
  simp only [KS.W01.encodeRat, List.length_append]
  omega

end KS.W19.SignedFloor

end

end OAI
