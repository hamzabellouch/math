import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentWordEvaluation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalWordTruncationEvaluation

namespace OAI

/-! # The universal logarithm evaluates to the actual finite logarithm -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] {c n : ℕ} (X : Fin n → A)
  (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0)

include hX

theorem weightedWordSubstitution_weight (p : RationalWords n) :
    weightedWordSubstitution X (rationalWordWeight c n p) = rationalWordEvaluation X p := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single w q =>
    rw [rationalWordWeight_single, map_smul, weightedWordSubstitution_weightedWord X hX,
      rationalWordEvaluation_single, FreeMonoid.lift_apply]

theorem nilpotent_word_exp_product_pow :
    ((List.ofFn (fun i => IsNilpotent.exp (X i))).prod - 1) ^ (c + 1) = 0 := by
  have ha := (weightedWordSubalgebra c n).sub_mem
    (weightedWordSubalgebra_exponentialProduct c n) (weightedWordSubalgebra c n).one_mem
  have h : weightedWordSubstitution X (truncatedWordExponentialProduct c n - 1) ^ (c + 1) = 0 := by
    rw [← weightedWordSubstitution_pow X hX ha, truncatedWordExponentialProduct_pow, map_zero]
  rw [map_sub, weightedWordSubstitution_exponentialProduct X hX,
    weightedWordSubstitution_one X hX] at h
  exact h

theorem rationalUniversalLogarithm_eval :
    rationalWordEvaluation X (rationalUniversalLogarithm c n) =
      finiteNilpotentLog (c + 1) ((List.ofFn (fun i => IsNilpotent.exp (X i))).prod - 1) := by
  rw [← weightedWordSubstitution_weight X hX, rationalWordWeight_universalLogarithm]
  change weightedWordSubstitution X (Polynomial.aeval _ _) = _
  rw [weightedWordSubstitution_aeval X hX
    ((weightedWordSubalgebra c n).sub_mem (weightedWordSubalgebra_exponentialProduct c n)
      (weightedWordSubalgebra c n).one_mem),
    map_sub, weightedWordSubstitution_exponentialProduct X hX, weightedWordSubstitution_one X hX]
  rfl

end PolycyclicRecognition

end

end OAI
