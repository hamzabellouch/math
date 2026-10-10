import OAI.Combinatorics.EditApproximation.Binary.BinaryFractionWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedNumericalParameters
import OAI.Combinatorics.EditApproximation.Geometry.ParameterAsymptotics
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The uniform program inspects only a logarithmically bounded prefix
of each accuracy word. An encoding exceeding this bound takes the exact
fallback, without first scanning or retaining its unbounded suffix. -/

namespace EditApproximation

/-- One step reads a constructor of the input word. -/


 theorem inspectBitPrefix_accepts (budget : ℕ) (word : List Bool) :
    (inspectBitPrefix budget word).1 = true ↔ word.length ≤ budget := by
  induction budget generalizing word with
  | zero => cases word <;> simp [inspectBitPrefix]
  | succ budget ih =>
    cases word with
    | nil => simp [inspectBitPrefix]
    | cons bit rest => simpa only [inspectBitPrefix, List.length_cons, Nat.add_le_add_iff_right] using ih rest

 theorem inspectBitPrefix_cost (budget : ℕ) (word : List Bool) :
    (inspectBitPrefix budget word).2 ≤ budget + 1 := by
  induction budget generalizing word with
  | zero => cases word <;> exact le_rfl
  | succ budget ih =>
    cases word with
    | nil => exact Nat.succ_le_succ (Nat.zero_le _)
    | cons bit rest => exact Nat.add_le_add_right (ih rest) 1

/-- On acceptance the input words are already bounded; returning the
input value only retains those bounded words. -/


 theorem inspectAccuracyWithWork_spec (budget : ℕ) (epsilon : BinaryFraction) :
    (inspectAccuracyWithWork budget epsilon).1 =
      if epsilon.width ≤ budget then some epsilon else none := by
  simp only [inspectAccuracyWithWork, BinaryFraction.width, max_le_iff]
  by_cases hn : epsilon.numerator.bits.length ≤ budget <;>
    by_cases hd : epsilon.denominator.length ≤ budget
  all_goals
    have hnum := inspectBitPrefix_accepts budget epsilon.numerator.bits
    have hden := inspectBitPrefix_accepts budget epsilon.denominator
    simp_all

 theorem inspectAccuracyWithWork_cost (budget : ℕ) (epsilon : BinaryFraction) :
    (inspectAccuracyWithWork budget epsilon).2 ≤ 2 * budget + 4 := by
  have hn := inspectBitPrefix_cost budget epsilon.numerator.bits
  have hd := inspectBitPrefix_cost budget epsilon.denominator
  change (inspectBitPrefix budget epsilon.numerator.bits).2 +
    (inspectBitPrefix budget epsilon.denominator).2 + 2 ≤ _
  omega

 theorem inspectAccuracy_eventually_accepts (epsilon : BinaryFraction) :
    ∀ᶠ N in Filter.atTop, (inspectAccuracyWithWork (inputHeight N) epsilon).1 = some epsilon := by
  filter_upwards [inputSmallLog_tendsto.eventually (Filter.eventually_ge_atTop epsilon.width)] with N hN
  rw [inspectAccuracyWithWork_spec, ite_eq_left (hN.trans (computed_smallLog_le_height N))]

end EditApproximation

end OAI
