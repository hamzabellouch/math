import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.DivisionLoopModel

namespace OAI

section

namespace KS.W19.SignedFloor

theorem loop_quotient (d xs : List Bool) (hd : 0 < bitsValue d) :
    bitsValue (DivisionLoop.process d xs.reverse [] []).1 = bitsValue xs / bitsValue d := by
  have h := DivisionLoop.process_payload_correct d xs hd
  symm
  apply Nat.div_eq_of_lt_le <;> nlinarith [h.1, h.2]

theorem old_quotient (d xs : List Bool) (hd : 0 < bitsValue d) :
    bitsValue (divideBits d xs).1 = bitsValue xs / bitsValue d := by
  have h := divideBits_correct d xs hd
  symm
  apply Nat.div_eq_of_lt_le <;> nlinarith [h.1, h.2]

theorem signed_quotient (z : Int) (d : Nat) (hd : 0 < d) :
    signedBitsValue (negativeOfInt z)
      (DivisionLoop.process (Computability.encodeNat d)
        (Computability.encodeNat (KS.W01.intPayload z)).reverse [] []).1 = z / (d : Int) := by
  have hpos : 0 < bitsValue (Computability.encodeNat d) := by simpa only [bitsValue_encodeNat] using hd
  have hmatch : bitsValue (DivisionLoop.process (Computability.encodeNat d)
      (Computability.encodeNat (KS.W01.intPayload z)).reverse [] []).1 =
      bitsValue (divideBits (Computability.encodeNat d) (Computability.encodeNat (KS.W01.intPayload z))).1 := by
    rw [loop_quotient _ _ hpos, old_quotient _ _ hpos]
  have h := divideSignedBits_intPayload_quotient z d hd
  have he : (divideSignedBits (negativeOfInt z) (Computability.encodeNat d)
      (Computability.encodeNat (KS.W01.intPayload z))).1 =
      (divideBits (Computability.encodeNat d) (Computability.encodeNat (KS.W01.intPayload z))).1 := by
    cases negativeOfInt z <;> rfl
  rw [he] at h
  simpa only [signedBitsValue, hmatch] using h

theorem encodeInt_constructor (z : Int) :
    KS.W01.encodeInt z = negativeOfInt z :: KS.W01.encodeNat (KS.W01.intPayload z) := by
  cases z <;> rfl

theorem encodeInt_signedBits (sign : Bool) (payload : List Bool) :
    KS.W01.encodeInt (signedBitsValue sign payload) =
      sign :: KS.W01.encodeNat (bitsValue payload) := by
  cases sign <;> rfl

theorem encodeRat_constructor (q : Rat) :
    KS.W01.encodeRat q = negativeOfInt q.num ::
      (KS.W01.encodeNat (KS.W01.intPayload q.num) ++ KS.W01.encodeNat q.den) := by
  rw [KS.W01.encodeRat, encodeInt_constructor]
  rfl

theorem floor_wire (q : Rat) :
    negativeOfInt q.num :: KS.W01.encodeNat
      (bitsValue (DivisionLoop.process (Computability.encodeNat q.den)
        (Computability.encodeNat (KS.W01.intPayload q.num)).reverse [] []).1) =
      KS.W01.encodeInt ⌊q⌋ := by
  rw [← encodeInt_signedBits, signed_quotient q.num q.den q.den_pos, Rat.floor_def']

end KS.W19.SignedFloor

end

end OAI
