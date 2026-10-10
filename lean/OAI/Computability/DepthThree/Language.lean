import OAI.Computability.DepthThree.LanguageParser
import OAI.Computability.DepthThree.AlgebraPolynomial
import OAI.Computability.DepthThree.Hash
import Mathlib.Algebra.Polynomial.Div

namespace OAI

namespace DepthThreeLowerBound

noncomputable section

open scoped BigOperators

namespace ParsedInput

def hashPolynomial (q : ParsedInput) : Polynomial (ZMod 2) :=
  BinaryAlgebra.pack fun i =>
    BinaryAlgebra.bitValue (BinaryHash.hashBool q.hashSeed q.data i)

def coefficientPolynomial (q : ParsedInput) (j : Fin q.coefficientCount) :
    Polynomial (ZMod 2) :=
  BinaryAlgebra.pack fun i => BinaryAlgebra.bitValue (q.coefficients j i)

def modulus (q : ParsedInput) : Polynomial (ZMod 2) :=
  BinaryAlgebra.inputPolynomialBits q.polynomial

theorem modulus_monic (q : ParsedInput) : q.modulus.Monic :=
  BinaryAlgebra.inputPolynomialBits_monic q.polynomial

theorem modulus_degree (q : ParsedInput) :
    q.modulus.degree = (q.ringDegree : WithBot ℕ) :=
  BinaryAlgebra.inputPolynomialBits_degree q.polynomial

def evaluationPolynomial (q : ParsedInput) : Polynomial (ZMod 2) :=
  ∑ j : Fin q.coefficientCount,
    q.coefficientPolynomial j * q.hashPolynomial ^ j.val

def evaluationRemainder (q : ParsedInput) : Polynomial (ZMod 2) :=
  q.evaluationPolynomial %ₘ q.modulus

theorem evaluationRemainder_degree_lt (q : ParsedInput) :
    q.evaluationRemainder.degree < (q.ringDegree : WithBot ℕ) := by
  rw [evaluationRemainder, ← q.modulus_degree]
  exact Polynomial.degree_modByMonic_lt _ q.modulus_monic

def evaluate (q : ParsedInput) : Bool :=
  decide (q.evaluationRemainder.coeff 0 = 0)

theorem evaluate_eq_true_iff (q : ParsedInput) :
    q.evaluate = true ↔ q.evaluationRemainder.coeff 0 = 0 := by
  simp only [evaluate, decide_eq_true_eq]

end ParsedInput

def language (w : List Bool) : Bool :=
  match parseInput w with
  | none => false
  | some q => q.evaluate

theorem language_of_not_fits {w : List Bool} (h : ¬InputFits w) :
    language w = false := by
  simp only [language, parseInput_of_not_fits h]

theorem language_of_fits {w : List Bool} (h : InputFits w) :
    language w = (decodeInput w).evaluate := by
  simp only [language, parseInput_of_fits h]

theorem language_eq_true_iff (w : List Bool) :
    language w = true ↔
      InputFits w ∧ (decodeInput w).evaluationRemainder.coeff 0 = 0 := by
  by_cases h : InputFits w
  · rw [language_of_fits h, ParsedInput.evaluate_eq_true_iff]
    simp only [h, true_and]
  · rw [language_of_not_fits h]
    simp only [Bool.false_eq_true, h, false_and]

end

end DepthThreeLowerBound

end OAI
