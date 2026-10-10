import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ArithmeticEncodingSize
import OAI.Analysis.MatrixSigning.Realization.RawRationalMachine

namespace OAI

section

namespace CurrentKS.RawRationalMachine
open KS.W19 KS.W30.BinaryRational KS.W01
open KS.W03.MachineCombinators

lemma normalizeMagnitude_lengths (num den : List Bool) (hd : 0 < bitsValue den) :
    (normalizeMagnitude num den).1.length ≤ num.length ∧
      (normalizeMagnitude num den).2.length ≤ den.length := by
  have ht : trimBits den ≠ [] := by
    intro h
    exact (Nat.ne_of_gt hd) ((KS.W30.BinaryGCD.trim_eq_nil_iff den).mp h)
  simp only [normalizeMagnitude, ite_eq_right ht]
  constructor
  · exact (trimBits_length_le _).trans (by rw [divideBits_quotient_length])
  · exact (trimBits_length_le _).trans (by rw [divideBits_quotient_length])

lemma canonical_lengths (a : RationalEntry) :
    (Computability.encodeNat a.value.num.natAbs).length ≤
        (Computability.encodeNat a.numerator.natAbs).length ∧
      (Computability.encodeNat a.value.den).length ≤
        (Computability.encodeNat a.denominator).length := by
  have he := normalize_eq_encodeMagnitude (magnitudeRecord a)
  rw [magnitudeRecord_value] at he
  have hn := congrArg RatBits.numerator he
  have hd := congrArg RatBits.denominator he
  simp only [magnitudeRecord, encodeMagnitude] at hn hd
  rw [←hn,←hd]
  exact normalizeMagnitude_lengths _ _ (by
    rw [bitsValue_encodeNat]; exact a.denominator_pos)

lemma entry_length (a : RationalEntry) :
    a.encode.length = 2*(KS.W06.RationalCompare.constructorBits a.numerator).length +
      2*(Computability.encodeNat a.denominator).length+3 := by
  rw [entry_wire]
  simp only [List.length_cons, List.length_append, length_frame]
  omega

lemma numerator_length (a : RationalEntry) :
    (Computability.encodeNat a.numerator.natAbs).length ≤
      (KS.W06.RationalCompare.constructorBits a.numerator).length+1 := by
  simpa only [KS.W06.RationalCompare.constructorBits,encodeNat_length_eq_size] using
    natAbs_size_le_payload_size_add_one a.numerator

lemma input_lengths (a : RationalEntry) :
    (Computability.encodeNat a.numerator.natAbs).length ≤ a.encode.length ∧
      (Computability.encodeNat a.denominator).length ≤ a.encode.length := by
  have hn := numerator_length a
  rw [entry_length]
  constructor <;> omega

lemma magnitude_length (s : Bool) (num : List Bool) :
    (MagnitudeProgram.result s num).length ≤ num.length+1 := by
  simpa only [MagnitudeProgram.result, List.length_nil, Nat.zero_max] using
    BinaryAdder.addBits_length_le s [] num

theorem value_wire_length (a : RationalEntry) :
    (encodeRat a.value).length ≤ a.encode.length+2 := by
  have hc := canonical_lengths a
  have hn := numerator_length a
  have hp := Nat.size_le_size (intPayload_le_natAbs a.value.num)
  rw [length_encodeRat]
  simp only [natPayloadLength_eq_size]
  rw [entry_length]
  simp only [encodeNat_length_eq_size] at hc hn ⊢
  omega

theorem ticks_le (a : RationalEntry) : ticks a a.encode.length ≤
    400*(a.encode.length+1)^3 := by
  have he := entry_length a
  have hi := input_lengths a
  have hc := canonical_lengths a
  have hm := magnitude_length (KS.W06.RationalCompare.negativeBit a.numerator)
    (KS.W06.RationalCompare.constructorBits a.numerator)
  have hl : a.encode.length+1 ≤ (a.encode.length+1)^3 := Nat.le_self_pow (by decide) _
  unfold ticks
  nlinarith

theorem polynomial_spec (a : RationalEntry) (tail : List Bool) :
    RunSpec program (state (a.encode++tail) [] [] [])
      (state tail (encodeRat a.value) [] []) (400*(a.encode.length+1)^3) :=
  (program_spec a tail a.encode.length (input_lengths a).1 (input_lengths a).2).mono
    (ticks_le a)

end CurrentKS.RawRationalMachine

end

end OAI
