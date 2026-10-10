import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentUniversalLogarithm

namespace OAI

/-! # Finite BCH in an associative algebra with vanishing long products

The universal logarithm constructs the finite Baker--Campbell--Hausdorff
coefficients.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℚ A] {c n : ℕ} (X : Fin n → A)

def finiteUniversalLiePolynomial : A :=
  ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
    ((d.val + 1 : ℚ)⁻¹ * (universalLogarithmCoefficient c n (d.val + 1)).coeff (wordOfFn w)) •
      evalBracketWord X (rightNestedWord d.val w)

variable (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0)
include hX

theorem rationalUniversalLogarithm_eval_lie :
    rationalWordEvaluation X (rationalUniversalLogarithm c n) =
      finiteUniversalLiePolynomial (c := c) X := by
  rw [rationalWord_evaluation_by_degrees X hX]
  simp_rw [rationalWordWeight_universalLogarithm]
  change (∑ d : Fin (c + 1), rationalWordEvaluation X (universalLogarithmCoefficient c n d.val)) = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, universalLogarithmCoefficient_zero, map_zero, zero_add]
  apply Finset.sum_congr rfl
  intro d _
  exact universalLogarithmCoefficient_lie_expansion c n d.val X

/-- A finite, universal right-nested Lie polynomial gives the exponential product. -/
theorem finite_associative_bch :
    (List.ofFn (fun i => IsNilpotent.exp (X i))).prod =
      IsNilpotent.exp (finiteUniversalLiePolynomial (c := c) X) := by
  have hnil := nilpotent_word_exp_product_pow X hX
  have he := exp_finiteNilpotentLog _ c hnil
  rw [add_sub_cancel] at he
  calc
    _ = IsNilpotent.exp (finiteNilpotentLog (c + 1)
        ((List.ofFn (fun i => IsNilpotent.exp (X i))).prod - 1)) := he.symm
    _ = IsNilpotent.exp (rationalWordEvaluation X (rationalUniversalLogarithm c n)) := by
      rw [rationalUniversalLogarithm_eval X hX]
    _ = _ := by rw [rationalUniversalLogarithm_eval_lie X hX]

theorem finiteUniversalLiePolynomial_pow :
    finiteUniversalLiePolynomial (c := c) X ^ (c + 1) = 0 := by
  rw [← rationalUniversalLogarithm_eval_lie X hX, rationalUniversalLogarithm_eval X hX]
  exact finiteNilpotentLog_pow _ c (nilpotent_word_exp_product_pow X hX)

end PolycyclicRecognition

end

end OAI
