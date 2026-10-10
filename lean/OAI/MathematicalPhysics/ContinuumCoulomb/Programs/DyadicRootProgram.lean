import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SquareRootProgram
import OAI.Computability.QuantumFactoring.BitStackRationalDivision

namespace OAI

/-! A computed dyadic square root of a nonnegative rational, with strict
error below one unit in the requested binary precision. Precision is unary;
numerator, denominator, and result are binary. -/

namespace ContinuumCoulomb.DyadicRootProgram
open ExactQuantumFactoring.BitStackProgram

def value (b N F : ℕ) : ℚ :=
  (SquareRootProgram.root (N * (2 ^ b) ^ 2 / F) : ℚ) / (2 : ℚ) ^ b

theorem value_error (b N F : ℕ) (hF : 0 < F) :
    0 ≤ Real.sqrt ((N : ℝ) / F) - (value b N F : ℝ) ∧
      Real.sqrt ((N : ℝ) / F) - (value b N F : ℝ) < 1 / (2 : ℝ) ^ b := by
  let p : ℕ := 2 ^ b
  let m : ℕ := N * p ^ 2 / F
  let r : ℕ := SquareRootProgram.root m
  have hp : (0 : ℝ) < p := by dsimp [p]; positivity
  have hFr : (0 : ℝ) < F := by exact_mod_cast hF
  have hlo : r ^ 2 * F ≤ N * p ^ 2 :=
    (Nat.mul_le_mul_right F (SquareRootProgram.root_spec m).1).trans (Nat.div_mul_le_self _ _)
  have hhi : N * p ^ 2 < (r + 1) ^ 2 * F :=
    (Nat.div_lt_iff_lt_mul hF).mp (SquareRootProgram.root_spec m).2
  have hlo' : (r : ℝ) ^ 2 * F ≤ (N : ℝ) * (p : ℝ) ^ 2 := by exact_mod_cast hlo
  have hhi' : (N : ℝ) * (p : ℝ) ^ 2 < ((r : ℝ) + 1) ^ 2 * F := by exact_mod_cast hhi
  have hrad : 0 ≤ (N : ℝ) / F := by positivity
  have hsquare : (Real.sqrt ((N : ℝ) / F) * p) ^ 2 * F = (N : ℝ) * (p : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrad]
    field_simp [hFr.ne']
  have hs : 0 ≤ Real.sqrt ((N : ℝ) / F) * p := by positivity
  have hslo : (r : ℝ) ^ 2 ≤ (Real.sqrt ((N : ℝ) / F) * p) ^ 2 := by
    apply (mul_le_mul_iff_left₀ hFr).mp
    rw [hsquare]
    exact hlo'
  have hshi : (Real.sqrt ((N : ℝ) / F) * p) ^ 2 < ((r : ℝ) + 1) ^ 2 := by
    apply (mul_lt_mul_iff_left₀ hFr).mp
    rw [hsquare]
    exact hhi'
  have hl : (r : ℝ) ≤ Real.sqrt ((N : ℝ) / F) * p := by
    nlinarith only [hslo, hs, show 0 ≤ (r : ℝ) by positivity]
  have hu : Real.sqrt ((N : ℝ) / F) * p < (r : ℝ) + 1 := by
    nlinarith only [hshi, hs, show 0 ≤ (r : ℝ) by positivity]
  have hvalue : (value b N F : ℝ) = (r : ℝ) / p := by
    simp only [value, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat, p, r, m,
      Nat.cast_pow, Nat.cast_ofNat]
  have hpcast : (p : ℝ) = (2 : ℝ) ^ b := by simp only [p, Nat.cast_pow, Nat.cast_ofNat]
  rw [hvalue, ← hpcast]
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hp).mpr hl)
  · apply (lt_div_iff₀ hp).mpr
    rw [sub_mul, div_mul_cancel₀ _ hp.ne']
    linarith

abbrev Input := ℕ × (ℕ × ℕ)

def rawCode : Input → List Bool := prodCode unaryCode (prodCode Nat.bits Nat.bits)

noncomputable def precisionProgram : Procedure rawCode unaryCode Prod.fst :=
  Procedure.first unaryCode (prodCode Nat.bits Nat.bits)

noncomputable def numeratorProgram : Procedure rawCode Nat.bits (fun x => x.2.1) :=
  (Procedure.first Nat.bits Nat.bits).comp
    (Procedure.second unaryCode (prodCode Nat.bits Nat.bits))

noncomputable def denominatorProgram : Procedure rawCode Nat.bits (fun x => x.2.2) :=
  (Procedure.second Nat.bits Nat.bits).comp
    (Procedure.second unaryCode (prodCode Nat.bits Nat.bits))

noncomputable def powerProgram : Procedure rawCode Nat.bits (fun x => 2 ^ x.1) :=
  (Procedure.binaryPow.comp (precisionProgram.pair
    (Procedure.constant rawCode Nat.bits 2))).congrFun (by intro x; rfl)

noncomputable def squareProgram : Procedure rawCode Nat.bits (fun x => (2 ^ x.1) ^ 2) :=
  (Procedure.binaryMul.comp (powerProgram.pair powerProgram)).congrFun (by intro x; exact (pow_two _).symm)

noncomputable def quotientProgram : Procedure rawCode Nat.bits
    (fun x => x.2.1 * (2 ^ x.1) ^ 2 / x.2.2) :=
  (Procedure.binaryDiv.comp ((Procedure.binaryMul.comp
    (numeratorProgram.pair squareProgram)).pair denominatorProgram)).congrFun (by intro x; rfl)

noncomputable def rootNumeratorProgram : Procedure rawCode Nat.bits
    (fun x => SquareRootProgram.root (x.2.1 * (2 ^ x.1) ^ 2 / x.2.2)) :=
  SquareRootProgram.rawProgram.comp quotientProgram

noncomputable def rawProgram : Procedure rawCode ratCode
    (fun x => value x.1 x.2.1 x.2.2) :=
  (Procedure.ratDiv.comp ((Procedure.natToRat.comp rootNumeratorProgram).pair
    (Procedure.natToRat.comp powerProgram))).congrFun (by
      intro x
      simp only [Function.comp_apply, value, Nat.cast_pow, Nat.cast_ofNat])

def fractionParameters : BinaryEncoding.Codec (ℕ × ℕ) :=
  BinaryEncoding.pair (BinaryEncoding.quoted BinaryEncoding.natural) BinaryEncoding.natural

def parameters : BinaryEncoding.Codec Input :=
  BinaryEncoding.pair (BinaryEncoding.quoted BinaryEncoding.unary) fractionParameters

theorem parameters_length (b N F : ℕ) :
    (parameters.encode (b, N, F)).length = 2 * b + 4 * N.size + 2 * F.size + 7 := by
  unfold parameters fractionParameters
  rw [BinaryEncoding.pair_length, BinaryEncoding.quoted_length, BinaryEncoding.unary_length,
    BinaryEncoding.pair_length, BinaryEncoding.quoted_length,
    BinaryEncoding.natural_length, BinaryEncoding.natural_length]
  dsimp only [Prod.fst, Prod.snd]
  omega

noncomputable def inputProgram : Procedure parameters.encode rawCode id := by
  let b := AmplificationProgram.inputProgram.comp
    (EncodingPrograms.quotedFirst BinaryEncoding.unary fractionParameters)
  let rest := EncodingPrograms.quotedSecond BinaryEncoding.unary fractionParameters
  let n := EncodingPrograms.naturalInput.comp
    ((EncodingPrograms.quotedFirst BinaryEncoding.natural BinaryEncoding.natural).comp rest)
  let f := EncodingPrograms.naturalInput.comp
    ((EncodingPrograms.quotedSecond BinaryEncoding.natural BinaryEncoding.natural).comp rest)
  exact (b.pair (n.pair f)).congrFun (by intro x; rfl)

def output : BinaryEncoding.Codec (ℤ × ℕ) :=
  BinaryEncoding.pair BinaryEncoding.integer BinaryEncoding.natural

noncomputable def rationalOutput : Procedure ratCode output.encode (fun q => (q.num, q.den)) := by
  let num := EncodingPrograms.integerOutput.comp Procedure.ratNum
  let den := EncodingPrograms.naturalOutput.comp Procedure.ratDen
  exact ((EncodingPrograms.appendPair BinaryEncoding.integer BinaryEncoding.natural).comp
    (num.pair den)).congrFun (by intro q; rfl)

/-- A concrete polynomial machine emits the canonical numerator and
denominator of the certified dyadic approximation. -/
noncomputable def certificate :
    Turing.TM2ComputableInPolyTime parameters.encode output.encode
      (fun x => ((value x.1 x.2.1 x.2.2).num, (value x.1 x.2.1 x.2.2).den)) :=
  (rationalOutput.comp (rawProgram.comp inputProgram)).toTM2

end ContinuumCoulomb.DyadicRootProgram

end OAI
