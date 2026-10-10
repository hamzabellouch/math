import OAI.Computability.DepthThree.AlgebraQuotient
import OAI.Computability.DepthThree.Language

namespace OAI

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound

namespace ParsedInput

abbrev QuotientRing (q : ParsedInput) := AdjoinRoot q.modulus

instance quotientRingFintype (q : ParsedInput) : Fintype q.QuotientRing :=
  BinaryAlgebra.inputQuotientFintype
    (fun i => BinaryAlgebra.bitValue (q.polynomial i))

def quotientHash (q : ParsedInput) : q.QuotientRing :=
  AdjoinRoot.mk q.modulus q.hashPolynomial

def quotientCoefficient (q : ParsedInput) (j : Fin q.coefficientCount) : q.QuotientRing :=
  AdjoinRoot.mk q.modulus (q.coefficientPolynomial j)

def quotientEvaluation (q : ParsedInput) : q.QuotientRing :=
  ∑ j : Fin q.coefficientCount, q.quotientCoefficient j * q.quotientHash ^ j.val

theorem quotientHash_eq_encode (q : ParsedInput) :
    q.quotientHash = BinaryAlgebra.encode
      (fun i => BinaryAlgebra.bitValue (q.polynomial i))
      (fun i => BinaryAlgebra.bitValue (BinaryHash.hashBool q.hashSeed q.data i)) := rfl

theorem quotientCoefficient_eq_encode (q : ParsedInput) (j : Fin q.coefficientCount) :
    q.quotientCoefficient j = BinaryAlgebra.encode
      (fun i => BinaryAlgebra.bitValue (q.polynomial i))
      (fun i => BinaryAlgebra.bitValue (q.coefficients j i)) := rfl

def coefficientBitsEquiv (q : ParsedInput) :
    (Fin q.ringDegree → Bool) ≃ q.QuotientRing :=
  (BinaryAlgebra.bitsEquivF2 (Fin q.ringDegree)).trans
    (BinaryAlgebra.coordinates
      (fun i => BinaryAlgebra.bitValue (q.polynomial i))).toEquiv.symm

@[simp] theorem coefficientBitsEquiv_apply (q : ParsedInput)
    (v : Fin q.ringDegree → Bool) :
    q.coefficientBitsEquiv v = BinaryAlgebra.encode
      (fun i => BinaryAlgebra.bitValue (q.polynomial i))
      (fun i => BinaryAlgebra.bitValue (v i)) := rfl

@[simp] theorem coefficientBitsEquiv_coefficient (q : ParsedInput)
    (j : Fin q.coefficientCount) :
    q.coefficientBitsEquiv (q.coefficients j) = q.quotientCoefficient j := rfl

@[simp] theorem quotientRing_card (q : ParsedInput) :
    Fintype.card q.QuotientRing = 2 ^ q.ringDegree :=
  BinaryAlgebra.bitQuotient_card q.polynomial

theorem quotientEvaluation_eq_mk (q : ParsedInput) :
    q.quotientEvaluation = AdjoinRoot.mk q.modulus q.evaluationPolynomial := by
  simp only [quotientEvaluation, evaluationPolynomial, quotientCoefficient, quotientHash,
    map_sum, map_mul, map_pow]

theorem representative_quotientEvaluation (q : ParsedInput) :
    BinaryAlgebra.quotientRepresentative q.modulus_monic q.quotientEvaluation =
      q.evaluationRemainder := by
  rw [quotientEvaluation_eq_mk, BinaryAlgebra.quotientRepresentative_mk]
  rfl

theorem degreeZero_quotientEvaluation (q : ParsedInput) :
    BinaryAlgebra.degreeZero q.modulus_monic q.quotientEvaluation =
      q.evaluationRemainder.coeff 0 := by
  rw [BinaryAlgebra.degreeZero_apply, representative_quotientEvaluation]

theorem quotient_degreeZero_one (q : ParsedInput) (hr : 0 < q.ringDegree) :
    BinaryAlgebra.degreeZero q.modulus_monic (1 : q.QuotientRing) = 1 := by
  apply BinaryAlgebra.degreeZero_one
  change 0 < (BinaryAlgebra.inputPolynomialBits q.polynomial).natDegree
  rw [BinaryAlgebra.inputPolynomialBits_natDegree]
  exact hr

theorem evaluate_eq_true_iff_degreeZero (q : ParsedInput) :
    q.evaluate = true ↔
      BinaryAlgebra.degreeZero q.modulus_monic q.quotientEvaluation = 0 := by
  rw [evaluate_eq_true_iff, degreeZero_quotientEvaluation]

end ParsedInput

theorem language_eq_true_iff_quotient (w : List Bool) :
    language w = true ↔ InputFits w ∧
      BinaryAlgebra.degreeZero (decodeInput w).modulus_monic
        (decodeInput w).quotientEvaluation = 0 := by
  rw [language_eq_true_iff, ParsedInput.degreeZero_quotientEvaluation]

end DepthThreeLowerBound

end

end OAI
