import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorParameters
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PolynomialTimeSize

namespace OAI

/-! Actual polynomial-time arithmetic for the explicitly scaled rational
mediator stage. Edge count, weight bound and inverse-error bound are unary;
the entering coefficient and emitted spoke are canonical binary rationals. -/

namespace ContinuumCoulomb.MediatorProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Input := ℕ × (ℕ × (ℕ × ℚ))

def rawCode : Input → List Bool := prodCode unaryCode
  (prodCode unaryCode (prodCode unaryCode ratCode))

noncomputable def rProgram : Procedure rawCode unaryCode Prod.fst :=
  Procedure.first unaryCode (prodCode unaryCode (prodCode unaryCode ratCode))

noncomputable def wProgram : Procedure rawCode unaryCode (fun x => x.2.1) :=
  (Procedure.first unaryCode (prodCode unaryCode ratCode)).comp
    (Procedure.second unaryCode (prodCode unaryCode (prodCode unaryCode ratCode)))

noncomputable def gProgram : Procedure rawCode unaryCode (fun x => x.2.2.1) :=
  ((Procedure.first unaryCode ratCode).comp
    (Procedure.second unaryCode (prodCode unaryCode ratCode))).comp
      (Procedure.second unaryCode (prodCode unaryCode (prodCode unaryCode ratCode)))

noncomputable def jProgram : Procedure rawCode ratCode (fun x => x.2.2.2) :=
  ((Procedure.second unaryCode ratCode).comp
    (Procedure.second unaryCode (prodCode unaryCode ratCode))).comp
      (Procedure.second unaryCode (prodCode unaryCode (prodCode unaryCode ratCode)))

noncomputable def cubeProgram : Procedure Nat.bits Nat.bits (fun n => n ^ 3) :=
  (Procedure.binaryPow.comp ((Procedure.constant Nat.bits unaryCode 3).pair
    (Procedure.identity Nat.bits))).congrFun (by intro n; rfl)

noncomputable def rCubeProgram : Procedure rawCode Nat.bits (fun x => (x.1 + 1) ^ 3) :=
  (cubeProgram.comp (Procedure.unaryToBits.comp
    (Procedure.unarySuccessor.comp rProgram))).congrFun (by intro x; rfl)

noncomputable def wCubeProgram : Procedure rawCode Nat.bits (fun x => x.2.1 ^ 3) :=
  (cubeProgram.comp (Procedure.unaryToBits.comp wProgram)).congrFun (by intro x; rfl)

noncomputable def cubicProductProgram : Procedure rawCode Nat.bits
    (fun x => (x.1 + 1) ^ 3 * x.2.1 ^ 3) :=
  Procedure.binaryMul.comp (rCubeProgram.pair wCubeProgram)

noncomputable def scaleProgram : Procedure rawCode Nat.bits
    (fun x => MediatorParameters.scale x.1 x.2.1 x.2.2.1) := by
  let product := Procedure.binaryMul.comp
    (cubicProductProgram.pair (Procedure.unaryToBits.comp gProgram))
  exact (Procedure.binaryMul.comp ((Procedure.constant rawCode Nat.bits 1048576).pair
    product)).congrFun (by
      intro x
      simp only [Function.comp_apply, id_eq, MediatorParameters.scale]
      ring)

noncomputable def deltaProgram : Procedure rawCode Nat.bits
    (fun x => MediatorParameters.delta x.1 x.2.1 x.2.2.1) :=
  (Procedure.binaryMul.comp (scaleProgram.pair scaleProgram)).congrFun
    (by intro x; exact (pow_two _).symm)

noncomputable def precisionProgram : Procedure rawCode unaryCode
    (fun x => MediatorParameters.precision x.1 x.2.2.1) :=
  (Procedure.unaryAdd.comp ((Procedure.unaryAdd.comp (rProgram.pair gProgram)).pair
    (Procedure.constant rawCode unaryCode 20))).congrFun (by intro x; rfl)

noncomputable def absoluteProgram : Procedure ratCode ratCode abs :=
  (Procedure.conditional (Procedure.intSign.comp Procedure.ratNum)
    Procedure.ratNeg (Procedure.identity ratCode)).congrFun (by
      intro q
      by_cases hn : q.num < 0
      · have hq : q < 0 := lt_of_not_ge (fun hq => (not_lt_of_ge (Rat.num_nonneg.mpr hq)) hn)
        simp [hn, abs_of_neg hq]
      · have hq : 0 ≤ q := Rat.num_nonneg.mp (le_of_not_gt hn)
        simp [hn, abs_of_nonneg hq])

noncomputable def deltaRationalProgram : Procedure rawCode ratCode
    (fun x => (MediatorParameters.delta x.1 x.2.1 x.2.2.1 : ℚ)) :=
  Procedure.natToRat.comp deltaProgram

noncomputable def radicandProgram : Procedure rawCode ratCode
    (fun x => MediatorParameters.radicand x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let product := Procedure.ratMul.comp (deltaRationalProgram.pair (absoluteProgram.comp jProgram))
  exact (Procedure.ratMul.comp ((Procedure.constant rawCode ratCode 2).pair product)).congrFun
    (by
      intro x
      simp only [Function.comp_apply, MediatorParameters.radicand]
      ring)

noncomputable def numeratorProgram : Procedure rawCode Nat.bits
    (fun x => (MediatorParameters.radicand x.1 x.2.1 x.2.2.1 x.2.2.2).num.toNat) :=
  ChargePrograms.intToNatProgram.comp (Procedure.ratNum.comp radicandProgram)

noncomputable def denominatorProgram : Procedure rawCode Nat.bits
    (fun x => (MediatorParameters.radicand x.1 x.2.1 x.2.2.1 x.2.2.2).den) :=
  Procedure.ratDen.comp radicandProgram

noncomputable def rootInputProgram : Procedure rawCode DyadicRootProgram.rawCode
    (fun x => (MediatorParameters.precision x.1 x.2.2.1,
      (MediatorParameters.radicand x.1 x.2.1 x.2.2.1 x.2.2.2).num.toNat,
      (MediatorParameters.radicand x.1 x.2.1 x.2.2.1 x.2.2.2).den)) :=
  precisionProgram.pair (numeratorProgram.pair denominatorProgram)

noncomputable def spokeProgram : Procedure rawCode ratCode
    (fun x => MediatorParameters.spoke x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  (DyadicRootProgram.rawProgram.comp rootInputProgram).congrFun (by intro x; rfl)

def rationalCodec : BinaryEncoding.Codec ℚ where
  encode q := (BinaryEncoding.pair BinaryEncoding.integer BinaryEncoding.natural).encode (q.num, q.den)
  read s := let (x, tail) := (BinaryEncoding.pair BinaryEncoding.integer BinaryEncoding.natural).read s
    (mkRat x.1 x.2, tail)
  read_encode q tail := by
    rw [(BinaryEncoding.pair BinaryEncoding.integer BinaryEncoding.natural).read_encode]
    dsimp only
    rw [Rat.mkRat_eq_div, Rat.num_div_den]

noncomputable def rationalInput : Procedure rationalCodec.encode ratCode id := by
  let num := EncodingPrograms.integerFirst BinaryEncoding.natural
  let den := EncodingPrograms.naturalInput.comp (EncodingPrograms.integerSecond BinaryEncoding.natural)
  let p := Procedure.makeRat.comp (num.pair den)
  exact (p.precompose (fun q : ℚ => (q.num, q.den))).congrFun (by
    intro q
    change mkRat q.num q.den = q
    rw [Rat.mkRat_eq_div, Rat.num_div_den])

noncomputable def rationalOutput : Procedure ratCode rationalCodec.encode id :=
  DyadicRootProgram.rationalOutput.result (by intro q; rfl)

def tailCodec : BinaryEncoding.Codec (ℕ × ℚ) :=
  BinaryEncoding.pair (BinaryEncoding.quoted BinaryEncoding.unary) rationalCodec

def middleCodec : BinaryEncoding.Codec (ℕ × (ℕ × ℚ)) :=
  BinaryEncoding.pair (BinaryEncoding.quoted BinaryEncoding.unary) tailCodec

def parameters : BinaryEncoding.Codec Input :=
  BinaryEncoding.pair (BinaryEncoding.quoted BinaryEncoding.unary) middleCodec

noncomputable def inputR : Procedure parameters.encode unaryCode Prod.fst :=
  AmplificationProgram.inputProgram.comp (EncodingPrograms.quotedFirst BinaryEncoding.unary middleCodec)

noncomputable def inputW : Procedure parameters.encode unaryCode (fun x => x.2.1) :=
  AmplificationProgram.inputProgram.comp
    ((EncodingPrograms.quotedFirst BinaryEncoding.unary tailCodec).comp
      (EncodingPrograms.quotedSecond BinaryEncoding.unary middleCodec))

noncomputable def inputG : Procedure parameters.encode unaryCode (fun x => x.2.2.1) :=
  AmplificationProgram.inputProgram.comp
    (((EncodingPrograms.quotedFirst BinaryEncoding.unary rationalCodec).comp
      (EncodingPrograms.quotedSecond BinaryEncoding.unary tailCodec)).comp
        (EncodingPrograms.quotedSecond BinaryEncoding.unary middleCodec))

noncomputable def inputJ : Procedure parameters.encode ratCode (fun x => x.2.2.2) :=
  rationalInput.comp
    (((EncodingPrograms.quotedSecond BinaryEncoding.unary rationalCodec).comp
      (EncodingPrograms.quotedSecond BinaryEncoding.unary tailCodec)).comp
        (EncodingPrograms.quotedSecond BinaryEncoding.unary middleCodec))

noncomputable def inputProgram : Procedure parameters.encode rawCode id :=
  inputR.pair (inputW.pair (inputG.pair inputJ))

noncomputable def publicDelta : Procedure parameters.encode BinaryEncoding.natural.encode
    (fun x => MediatorParameters.delta x.1 x.2.1 x.2.2.1) :=
  (EncodingPrograms.naturalOutput.comp (deltaProgram.comp inputProgram)).congrFun (by intro x; rfl)

noncomputable def publicSpoke : Procedure parameters.encode rationalCodec.encode
    (fun x => MediatorParameters.spoke x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  (rationalOutput.comp (spokeProgram.comp inputProgram)).congrFun (by intro x; rfl)

def output : BinaryEncoding.Codec (ℕ × ℚ) := BinaryEncoding.pair BinaryEncoding.natural rationalCodec

noncomputable def pairedProgram : Procedure parameters.encode
    (prodCode BinaryEncoding.natural.encode rationalCodec.encode)
    (fun x => (MediatorParameters.delta x.1 x.2.1 x.2.2.1,
      MediatorParameters.spoke x.1 x.2.1 x.2.2.1 x.2.2.2)) := publicDelta.pair publicSpoke

/-- The actual finite machine, including rational normalization and square
root search, has polynomial runtime in the explicit unary/binary inputs. -/
noncomputable def certificate :
    Turing.TM2ComputableInPolyTime parameters.encode output.encode
      (fun x => (MediatorParameters.delta x.1 x.2.1 x.2.2.1,
        MediatorParameters.spoke x.1 x.2.1 x.2.2.1 x.2.2.2)) :=
  ((EncodingPrograms.appendPair BinaryEncoding.natural rationalCodec).comp pairedProgram).toTM2

theorem parameters_length (x : Input) :
    (parameters.encode x).length = 2 * x.1 + 2 * x.2.1 + 2 * x.2.2.1 + 9 +
      (rationalCodec.encode x.2.2.2).length := by
  simp only [parameters, middleCodec, tailCodec, BinaryEncoding.pair_length,
    BinaryEncoding.quoted_length, BinaryEncoding.unary_length]
  omega

/-- The emitted coefficient code has a polynomial length bound obtained
from the actual finite machine, including the square-root computation. -/
theorem output_polynomial_size : ∃ p : Polynomial ℕ, ∀ x : Input,
    (output.encode (MediatorParameters.delta x.1 x.2.1 x.2.2.1,
      MediatorParameters.spoke x.1 x.2.1 x.2.2.1 x.2.2.2)).length ≤
        p.eval (parameters.encode x).length := by
  refine ⟨Polynomial.X + certificate.time * Polynomial.C (TM2Size.programPushes certificate.tm), ?_⟩
  intro x
  simpa only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
    using TM2Size.output_length certificate x

end ContinuumCoulomb.MediatorProgram

end OAI
