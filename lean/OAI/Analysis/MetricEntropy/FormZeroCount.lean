import OAI.Analysis.MetricEntropy.FormPolynomials
import OAI.Analysis.MetricEntropy.PolynomialZeroBound
import OAI.Analysis.MetricEntropy.DirectionTuples
import Mathlib.Logic.Equiv.Prod

namespace OAI

/-!
# Actual repeated-tuple zero events

The finite sample is a family of vectors. Currying identifies it with the
scalar assignments of the literal tuple polynomial. No injectivity or
nonzero-coordinate assumption is made on the sampled vectors or tuple indices.
-/

noncomputable section

namespace MetricEntropyDuality

variable {p r h u : ℕ} [Fact p.Prime]

/-- The original vector-sample event has exactly the polynomial zero count. -/
theorem tupleEvent_form_zero_card (F : SymmetricForm (ZMod p) r h)
    (a : Fin h → Fin u) :
    (tupleEvent (fun v => SymmetricForm.eval F v = 0) a).card =
      (polynomialZeros (tuplePolynomial F a)).card := by
  classical
  apply Finset.card_equiv (Equiv.curry (Fin u) (Fin r) (ZMod p)).symm
  intro t
  simp only [mem_tupleEvent, mem_polynomialZeros]
  change SymmetricForm.eval F (fun j => t (a j)) = 0 ↔
    MvPolynomial.eval (fun z => t z.1 z.2) (tuplePolynomial F a) = 0
  rw [eval_tuplePolynomial]

/-- The literal number of samples is the number of scalar assignments. -/
theorem card_direction_samples :
    Fintype.card (Fin u → Fin r → ZMod p) =
      p ^ Fintype.card (Fin u × Fin r) := by
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card,
    Fintype.card_prod]
  rw [← pow_mul, Nat.mul_comm r u]

/-- Cross-multiplied finite zero count, including every repeated-index tuple. -/
theorem tupleEvent_form_zero_card_mul_le (hp : h < p)
    (F : SymmetricForm (ZMod p) r h) (hF : F ≠ 0)
    (a : Fin h → Fin u) :
    p * (tupleEvent (fun v => SymmetricForm.eval F v = 0) a).card ≤
      h * Fintype.card (Fin u → Fin r → ZMod p) := by
  rw [tupleEvent_form_zero_card, card_direction_samples]
  exact polynomial_zero_card_mul_le_of_totalDegree_le (tuplePolynomial F a)
    (tuplePolynomial_ne_zero hp F hF a) (totalDegree_tuplePolynomial_le F a)

/-- Real zero count for the actual vector sample. -/
theorem tupleEvent_form_zero_card_real_le (hp : h < p)
    (F : SymmetricForm (ZMod p) r h) (hF : F ≠ 0)
    (a : Fin h → Fin u) :
    ((tupleEvent (fun v => SymmetricForm.eval F v = 0) a).card : ℝ) ≤
      (h : ℝ) / p * (Fintype.card (Fin u → Fin r → ZMod p) : ℝ) := by
  rw [tupleEvent_form_zero_card, card_direction_samples]
  exact polynomial_zero_card_real_le (tuplePolynomial F a)
    (tuplePolynomial_ne_zero hp F hF a) (totalDegree_tuplePolynomial_le F a)

/-- Uniform probability of a zero evaluation is at most `h/p`, with repetitions
allowed in `a`. The denominator is the full finite vector-sample cardinality. -/
theorem tupleEvent_form_zero_proportion_le (hp : h < p)
    (F : SymmetricForm (ZMod p) r h) (hF : F ≠ 0)
    (a : Fin h → Fin u) :
    ((tupleEvent (fun v => SymmetricForm.eval F v = 0) a).card : ℝ) /
      (Fintype.card (Fin u → Fin r → ZMod p) : ℝ) ≤ (h : ℝ) / p := by
  rw [tupleEvent_form_zero_card, card_direction_samples]
  exact polynomial_zero_proportion_le (tuplePolynomial F a)
    (tuplePolynomial_ne_zero hp F hF a) (totalDegree_tuplePolynomial_le F a)

end MetricEntropyDuality

end

end OAI
