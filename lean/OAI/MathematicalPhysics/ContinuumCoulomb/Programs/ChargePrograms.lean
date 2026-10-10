import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.EncodingPrograms
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.BinaryWellCharges
import OAI.Computability.QuantumFactoring.BitStackRationalDivision
import OAI.Computability.QuantumFactoring.BitStackRationalFloor

namespace OAI

/-! Actual polynomial-time stack programs for the two rounded binary-well
charges. The geometric scale is unary and the number of sites is binary.
The output is the pair of binary natural-number codes. -/

namespace ContinuumCoulomb
namespace ChargePrograms
open ExactQuantumFactoring.BitStackProgram

def parameters : BinaryEncoding.Codec (ℕ × ℕ) :=
  BinaryEncoding.pair (BinaryEncoding.quoted BinaryEncoding.unary) BinaryEncoding.natural

theorem parameters_encoding (x : ℕ × ℕ) : parameters.encode x =
    prodCode BinaryEncoding.unary.encode BinaryEncoding.natural.encode x := by
  change BinaryEncoding.encodeDigits (BinaryEncoding.unary.encode x.1) ++ _ = _
  rw [AmplificationProgram.encodeDigits_quote]
  rfl

theorem parameters_length (D m : ℕ) :
    (parameters.encode (D, m)).length = 2 * D + 2 * m.size + 4 := by
  unfold parameters
  rw [BinaryEncoding.pair_length, BinaryEncoding.quoted_length,
    BinaryEncoding.unary_length, BinaryEncoding.natural_length]
  dsimp only [Prod.fst, Prod.snd]
  omega

/-- Clamp a signed binary integer to a natural number. -/
noncomputable def intToNatProgram : Procedure intCode Nat.bits Int.toNat :=
  (Procedure.conditional Procedure.intSign
    (Procedure.constant intCode Nat.bits 0) Procedure.intAbs).congrFun (by
      intro z
      cases z <;> simp)

/-- Ties round upward, exactly as the manuscript's rational charge function. -/
noncomputable def rationalRoundProgram : Procedure ratCode intCode (fun q => round q) :=
  (Procedure.ratFloor.comp (Procedure.ratAdd.comp
    ((Procedure.identity ratCode).pair (Procedure.constant ratCode ratCode (1 / 2))))).congrFun
      (by intro q; exact (round_eq q).symm)

noncomputable def scaledRoundProgram : Procedure (prodCode Nat.bits ratCode) Nat.bits
    (fun x => rationalRoundedScaledCharge x.1 x.2) := by
  let z := Procedure.natToRat.comp (Procedure.first Nat.bits ratCode)
  let q := Procedure.second Nat.bits ratCode
  exact (intToNatProgram.comp (rationalRoundProgram.comp
    (Procedure.ratMul.comp (z.pair q)))).congrFun (by intro x; rfl)

def rawParameters : (ℕ × ℕ) → List Bool := prodCode unaryCode Nat.bits

noncomputable def dProgram : Procedure rawParameters unaryCode Prod.fst :=
  Procedure.first unaryCode Nat.bits

noncomputable def mProgram : Procedure rawParameters Nat.bits Prod.snd :=
  Procedure.second unaryCode Nat.bits

noncomputable def amplificationProgram : Procedure rawParameters Nat.bits
    (fun x => binaryAmplification x.1) :=
  (AmplificationProgram.rawProgram.comp dProgram).congrFun (by intro x; rfl)

noncomputable def dRationalProgram : Procedure rawParameters ratCode (fun x => (x.1 : ℚ)) :=
  (Procedure.natToRat.comp (Procedure.unaryToBits.comp dProgram)).congrFun (by intro x; rfl)

noncomputable def mRationalProgram : Procedure rawParameters ratCode (fun x => (x.2 : ℚ)) :=
  (Procedure.natToRat.comp mProgram).congrFun (by intro x; rfl)

noncomputable def fractionProgram (c : ℕ) : Procedure rawParameters ratCode
    (fun x => (c : ℚ) * x.2 / x.1) := by
  let multiple := Procedure.ratMul.comp
    ((Procedure.constant rawParameters ratCode (c : ℚ)).pair mRationalProgram)
  exact (Procedure.ratDiv.comp (multiple.pair dRationalProgram)).congrFun (by intro x; rfl)

noncomputable def primaryRatioProgram : Procedure rawParameters ratCode
    (fun x => 1 - 500 * x.2 / (x.1 : ℚ)) :=
  (Procedure.ratSub.comp ((Procedure.constant rawParameters ratCode 1).pair
    (fractionProgram 500))).congrFun (by intro x; rfl)

noncomputable def primaryRawProgram : Procedure rawParameters Nat.bits
    (fun x => binaryPrimaryCharge x.1 x.2) :=
  (scaledRoundProgram.comp (amplificationProgram.pair primaryRatioProgram)).congrFun (by intro x; rfl)

noncomputable def secondaryRawProgram : Procedure rawParameters Nat.bits
    (fun x => binarySecondaryCharge x.1 x.2) :=
  (scaledRoundProgram.comp (amplificationProgram.pair (fractionProgram 1000))).congrFun (by intro x; rfl)

/-- Parse the actual marker bits of a binary natural number. -/
noncomputable def naturalInputProgram : Procedure BinaryEncoding.natural.encode Nat.bits id :=
  EncodingPrograms.naturalInput

noncomputable def inputProgram : Procedure parameters.encode rawParameters id := by
  let d := AmplificationProgram.inputProgram.comp
    (Procedure.first BinaryEncoding.unary.encode BinaryEncoding.natural.encode)
  let m := naturalInputProgram.comp
    (Procedure.second BinaryEncoding.unary.encode BinaryEncoding.natural.encode)
  exact (d.pair m).congrEncoding (fun x => (parameters_encoding x).symm) (by intro x; rfl)

noncomputable def naturalOutputProgram : Procedure Nat.bits BinaryEncoding.natural.encode id :=
  EncodingPrograms.naturalOutput

def output : BinaryEncoding.Codec (ℕ × ℕ) :=
  BinaryEncoding.pair BinaryEncoding.natural BinaryEncoding.natural

noncomputable def primaryProgram : Procedure parameters.encode BinaryEncoding.natural.encode
    (fun x => binaryPrimaryCharge x.1 x.2) :=
  (naturalOutputProgram.comp (primaryRawProgram.comp inputProgram)).congrFun (by intro x; rfl)

noncomputable def secondaryProgram : Procedure parameters.encode BinaryEncoding.natural.encode
    (fun x => binarySecondaryCharge x.1 x.2) :=
  (naturalOutputProgram.comp (secondaryRawProgram.comp inputProgram)).congrFun (by intro x; rfl)

noncomputable def pairProgram : Procedure parameters.encode
    (prodCode BinaryEncoding.natural.encode BinaryEncoding.natural.encode)
    (fun x => (binaryPrimaryCharge x.1 x.2, binarySecondaryCharge x.1 x.2)) :=
  primaryProgram.pair secondaryProgram

/-- Both physical charges, including rational scaling and integer rounding,
are computed by a finite Boolean-stack program with a polynomial runtime. -/
noncomputable def program : Procedure parameters.encode output.encode
    (fun x => (binaryPrimaryCharge x.1 x.2, binarySecondaryCharge x.1 x.2)) :=
  ((EncodingPrograms.appendPair BinaryEncoding.natural BinaryEncoding.natural).comp
    pairProgram).congrFun (by intro x; rfl)

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime parameters.encode output.encode
      (fun x => (binaryPrimaryCharge x.1 x.2, binarySecondaryCharge x.1 x.2)) := program.toTM2

theorem output_length (D m : ℕ) :
    (output.encode (binaryPrimaryCharge D m, binarySecondaryCharge D m)).length =
      2 * (binaryPrimaryCharge D m).size + 2 * (binarySecondaryCharge D m).size + 2 := by
  unfold output
  rw [BinaryEncoding.pair_length, BinaryEncoding.natural_length, BinaryEncoding.natural_length]
  dsimp only [Prod.fst, Prod.snd]
  omega

theorem output_length_le {D m : ℕ} (hm : 0 < m) (hscale : 2002 * m ≤ D) :
    (output.encode (binaryPrimaryCharge D m, binarySecondaryCharge D m)).length ≤ 8 * D + 10 := by
  rw [output_length]
  obtain ⟨hp, hs⟩ := binaryWellCharges_bit_length hm hscale
  omega

end ChargePrograms
end ContinuumCoulomb

end OAI
