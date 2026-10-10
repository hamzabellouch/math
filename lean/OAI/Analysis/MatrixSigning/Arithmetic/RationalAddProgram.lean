import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ArithmeticEncodingSize
import OAI.Analysis.MatrixSigning.Arithmetic.RationalAddSigned
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMagnitudeCorrect
import OAI.Analysis.MatrixSigning.Arithmetic.SignedRationalSerializer

namespace OAI

namespace KS.W13.RationalAdd
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (magnitude product negativeBit constructorBits pairBits)

def preNormalizeProgram : Program 16 :=
  compose (compose (compose prepareProgram productsProgram) clearProductsProgram) signedProgram

def preNormalizeTicks (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : ℕ :=
  let a := magnitude sa na
  let b := magnitude sb nb
  ((KS.W06.RationalCompare.parseTicks na da nb db + (2 * na.length + 4) + (2 * nb.length + 4)) +
    productsTicks a da b db + clearProductsTicks a da b db) +
    signedBudget (product a db) (product b da) (product da db)

def rawInputSum (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    KS.W30.BinaryRational.RatBits := rawSum sa (magnitude sa na) da sb (magnitude sb nb) db

theorem preNormalize_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    let x := rawInputSum sa na da sb nb db
    RunSpec preNormalizeProgram (inputState (pairBits sa na da sb nb db))
      (readyState x.negative x.numerator x.denominator) (preNormalizeTicks sa na da sb nb db) := by
  exact (((prepare_spec sa na da sb nb db).compose
    (products_spec sa (magnitude sa na) da sb (magnitude sb nb) db)).compose
    (clearProducts_spec sa (magnitude sa na) da sb (magnitude sb nb) db)).compose
    (signed_spec sa sb (product (magnitude sa na) db) (product (magnitude sb nb) da) (product da db))

def payloadBound (na da nb db : List Bool) : ℕ := na.length + da.length + nb.length + db.length + 3

theorem rawInputSum_bounds (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    let x := rawInputSum sa na da sb nb db
    KS.W19.CanonicalBits x.numerator ∧ KS.W19.CanonicalBits x.denominator ∧
      x.numerator.length ≤ payloadBound na da nb db ∧ x.denominator.length ≤ payloadBound na da nb db := by
  dsimp only
  have ha := KS.W06.RationalCompare.magnitude_length_le sa na
  have hb := KS.W06.RationalCompare.magnitude_length_le sb nb
  have hl := KS.W06.RationalCompare.product_length_le (magnitude sa na) db
  have hr := KS.W06.RationalCompare.product_length_le (magnitude sb nb) da
  have hd := KS.W06.RationalCompare.product_length_le da db
  have hn := signedNumerator_length_le sa (product (magnitude sa na) db) sb (product (magnitude sb nb) da)
  refine ⟨signedNumerator_canonical _ _ _ _, KS.W19.canonicalBits_encodeNat _, ?_, ?_⟩
  · change (signedNumerator sa (product (magnitude sa na) db)
      sb (product (magnitude sb nb) da)).2.length ≤
        na.length + da.length + nb.length + db.length + 3
    omega
  · change (product da db).length ≤ na.length + da.length + nb.length + db.length + 3
    omega

def normalizeProgram : Program 16 :=
  KS.W29.FixedSequential.liftPorts KS.W30.RationalMagnitudeMachine.program corePorts

def serializeProgram : Program 16 :=
  KS.W29.FixedSequential.liftPorts KS.W01.SignedRationalSerializer.program corePorts

def outputState (wire : List Bool) : Fin 16 → List Bool :=
  extend (KS.W01.SignedRationalSerializer.outputState wire) [] [] []

def program : Program 16 := compose (compose preNormalizeProgram normalizeProgram) serializeProgram

def machine : Machine := program.toMachine

def totalTicks (q r : ℚ) : ℕ :=
  preNormalizeTicks (negativeBit q.num) (constructorBits q.num) (Computability.encodeNat q.den)
    (negativeBit r.num) (constructorBits r.num) (Computability.encodeNat r.den) +
  300 * (payloadBound (constructorBits q.num) (Computability.encodeNat q.den)
    (constructorBits r.num) (Computability.encodeNat r.den) + 1) ^ 3 +
  16 * ((Computability.encodeNat (q+r).num.natAbs).length +
    (Computability.encodeNat (q+r).den).length + 1)

theorem full_spec (q r : ℚ) :
    RunSpec program (inputState (KS.W01.encodeRat q ++ KS.W01.encodeRat r))
      (outputState (KS.W01.encodeRat (q+r))) (totalTicks q r) := by
  let sa := negativeBit q.num
  let na := constructorBits q.num
  let da := Computability.encodeNat q.den
  let sb := negativeBit r.num
  let nb := constructorBits r.num
  let db := Computability.encodeNat r.den
  let x := rawInputSum sa na da sb nb db
  have hv : x.value = q+r := rawSum_encoded_value q r
  obtain ⟨hnc, hdc, hn, hd⟩ := rawInputSum_bounds sa na da sb nb db
  have hnorm := core_spec KS.W30.RationalMagnitudeMachine.program _ _ [] [] [] _
    (KS.W30.RationalMagnitudeMachine.normalizes_to_rational_encoding x
      (payloadBound na da nb db) hnc hdc hn hd)
  rw [hv] at hnorm
  have hserialize := core_spec KS.W01.SignedRationalSerializer.program _ _ [] [] [] _
    (KS.W01.SignedRationalSerializer.serializes_rational (q+r))
  have h := ((preNormalize_spec sa na da sb nb db).compose hnorm).compose hserialize
  simp only [sa, na, da, sb, nb, db, KS.W06.RationalCompare.pairBits_encodeRat] at h
  exact h

theorem output_length_le (q r : ℚ) :
    (KS.W01.encodeRat (q+r)).length ≤
      4 * (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length + 9 := by
  simpa [KS.W01.ratLength, List.length_append] using KS.W01.ratLength_add_le q r

end KS.W13.RationalAdd

end OAI
