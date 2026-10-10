import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.Abel

namespace OAI

/-! # The right-nested commutator projection of rational words -/

noncomputable section
namespace PolycyclicRecognition

abbrev RationalWords (n : ℕ) := MonoidAlgebra ℚ (FreeMonoid (Fin n))

variable {A : Type*} [Ring A] [Algebra ℚ A] {n : ℕ} (X : Fin n → A)

def wordRightLie : List (Fin n) → A
  | [] => 0
  | [i] => X i
  | i :: j :: l => X i * wordRightLie (j :: l) - wordRightLie (j :: l) * X i

def wordLieProjection : RationalWords n →ₗ[ℚ] A :=
  (Finsupp.linearCombination ℚ (fun w : FreeMonoid (Fin n) => wordRightLie X w.toList)).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem wordLieProjection_single (w : FreeMonoid (Fin n)) (q : ℚ) :
    wordLieProjection X (MonoidAlgebra.single w q) = q • wordRightLie X w.toList := by
  change Finsupp.linearCombination ℚ _ (Finsupp.single w q) = _
  exact Finsupp.linearCombination_single (R := ℚ)
    (v := fun w : FreeMonoid (Fin n) => wordRightLie X w.toList) q w

def rationalWordLetter (i : Fin n) : RationalWords n :=
  MonoidAlgebra.single (FreeMonoid.of i) 1

theorem wordLieProjection_letter_mul (i : Fin n) (p : RationalWords n) :
    wordLieProjection X (rationalWordLetter i * p) =
      X i * wordLieProjection X p - wordLieProjection X p * X i + p.coeff 1 • X i := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change wordLieProjection X (rationalWordLetter i * MonoidAlgebra.single w 1) =
      X i * wordLieProjection X (MonoidAlgebra.single w 1) -
        wordLieProjection X (MonoidAlgebra.single w 1) * X i +
        (MonoidAlgebra.single w (1 : ℚ)).coeff 1 • X i
    rw [rationalWordLetter, MonoidAlgebra.single_mul_single, one_mul,
      wordLieProjection_single, wordLieProjection_single, one_smul, one_smul]
    cases hw : w.toList with
    | nil =>
      have hw1 : w = 1 := FreeMonoid.toList.injective hw
      subst w
      simp [wordRightLie, MonoidAlgebra.coeff_single]
    | cons j l =>
      have hw1 : w ≠ 1 := by
        intro h
        simp [h] at hw
      simp [wordRightLie, hw, MonoidAlgebra.coeff_single, hw1]
  | add p q hp hq =>
    simp only [mul_add, map_add, hp, hq, add_mul, MonoidAlgebra.coeff_add,
      Finsupp.add_apply, add_smul]
    abel
  | smul r p hp =>
    simp only [mul_smul_comm, map_smul, hp, smul_mul_assoc, MonoidAlgebra.coeff_smul,
      Finsupp.smul_apply, smul_sub, smul_add, smul_smul, Algebra.mul_smul_comm, smul_eq_mul]

end PolycyclicRecognition

end

end OAI
