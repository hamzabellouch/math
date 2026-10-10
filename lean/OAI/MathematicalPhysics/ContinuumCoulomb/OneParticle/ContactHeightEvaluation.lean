import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactHeightBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedEvaluationBudget

namespace OAI

/-! A concrete rational evaluator for the one-dimensional height residual.
There are exactly four dyadic square-root calls; all other terms are exact. -/

noncomputable section
namespace ContinuumCoulomb.ContactHeightEvaluation

abbrev Environment := ℕ × (List ℚ × ℚ)

def lengthAt (e : Environment) (k : ℕ) : ℚ := (e.2.1.drop k).headD 1

def rootSample (e : Environment) (h : ℚ) (k : ℕ) : ℚ :=
  RationalSquareRoot.value (CalibratedEvaluation.rootPrecision e.1, (lengthAt e k) ^ 2 - h ^ 2)

def value (e : Environment) (h : ℚ) : ℚ :=
  lengthAt e 0 + lengthAt e 1 + lengthAt e 4 + lengthAt e 7 + lengthAt e 8 +
    rootSample e h 2 + rootSample e h 3 + rootSample e h 5 + rootSample e h 6 - e.2.2

def residual (e : Environment) (h : ℝ) : ℝ :=
  adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h - (e.2.2 : ℝ)

theorem rootSample_error (e : Environment) (h : ℚ) (k : ℕ)
    (hl : 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hh : (h : ℝ) ∈ Set.Icc (2 / 5) (3 / 4)) :
    |(rootSample e h k : ℝ) - adjustedContactForward (lengthAt e k) h| ≤
      (2 : ℝ)⁻¹ ^ CalibratedEvaluation.rootPrecision e.1 := by
  have hlow : (99 / 100 : ℝ) ≤ lengthAt e k := by
    norm_num [contactLengthTolerance] at hl
    linarith
  have hrad : (0 : ℝ) ≤ (lengthAt e k : ℝ) ^ 2 - (h : ℝ) ^ 2 := by
    have hh0 : (0 : ℝ) ≤ h := by linarith [hh.1]
    nlinarith [hh.2]
  have hradQ : (0 : ℚ) ≤ (lengthAt e k) ^ 2 - h ^ 2 := by exact_mod_cast hrad
  have he := RationalSquareRoot.value_error (CalibratedEvaluation.rootPrecision e.1) hradQ
  simpa only [rootSample, adjustedContactForward, Rat.cast_sub, Rat.cast_pow] using he

private theorem four_errors {a b c d E : ℝ}
    (ha : |a| ≤ E) (hb : |b| ≤ E) (hc : |c| ≤ E) (hd : |d| ≤ E) :
    |a + b + c + d| ≤ 4 * E := by
  have h₁ := (abs_add_le a b).trans (add_le_add ha hb)
  have h₂ := (abs_add_le c d).trans (add_le_add hc hd)
  have h := (abs_add_le (a + b) (c + d)).trans (add_le_add h₁ h₂)
  rw [add_assoc (a + b) c d]
  exact h.trans_eq (by ring)

theorem approximation_error (e : Environment) (h : ℚ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hh : (h : ℝ) ∈ Set.Icc (2 / 5) (3 / 4)) :
    |(value e h : ℝ) - residual e h| ≤ ((e.1 : ℝ) + 1)⁻¹ := by
  have h₂ := rootSample_error e h 2 (hl 2 (by norm_num)) hh
  have h₃ := rootSample_error e h 3 (hl 3 (by norm_num)) hh
  have h₅ := rootSample_error e h 5 (hl 5 (by norm_num)) hh
  have h₆ := rootSample_error e h 6 (hl 6 (by norm_num)) hh
  have heq : (value e h : ℝ) - residual e h =
      ((rootSample e h 2 : ℝ) - adjustedContactForward (lengthAt e 2) h) +
      ((rootSample e h 3 : ℝ) - adjustedContactForward (lengthAt e 3) h) +
      ((rootSample e h 5 : ℝ) - adjustedContactForward (lengthAt e 5) h) +
      ((rootSample e h 6 : ℝ) - adjustedContactForward (lengthAt e 6) h) := by
    norm_num [value, residual, adjustedContactSpan, adjustedContactStepX,
      Finset.sum_range_succ, Rat.cast_add, Rat.cast_sub]
    ring
  rw [heq]
  apply (four_errors h₂ h₃ h₅ h₆).trans
  have hb := mul_le_mul_of_nonneg_left (CalibratedEvaluation.root_budget e.1)
    (show (0 : ℝ) ≤ 4 by norm_num)
  convert hb using 1
  field_simp [show (e.1 : ℝ) + 1 ≠ 0 by positivity]

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
