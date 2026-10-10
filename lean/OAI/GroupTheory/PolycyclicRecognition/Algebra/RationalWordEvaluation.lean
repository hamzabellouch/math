import OAI.GroupTheory.PolycyclicRecognition.Geometry.WordLieProjection
import Mathlib.Algebra.MonoidAlgebra.Basic

namespace OAI

/-! # Evaluation and the empty-word coefficient of rational words -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] {n : ℕ}

def rationalWordEvaluation (X : Fin n → A) : RationalWords n →ₐ[ℚ] A :=
  MonoidAlgebra.lift ℚ A (FreeMonoid (Fin n)) (FreeMonoid.lift X)

theorem rationalWordEvaluation_single (X : Fin n → A)
    (w : FreeMonoid (Fin n)) (q : ℚ) :
    rationalWordEvaluation X (MonoidAlgebra.single w q) = q • (w.toList.map X).prod := by
  rw [rationalWordEvaluation, MonoidAlgebra.lift_single, FreeMonoid.lift_apply]

def rationalWordAugmentation : RationalWords n →ₐ[ℚ] ℚ :=
  rationalWordEvaluation (fun _ => 0)

theorem rationalWordAugmentation_eq_coeff (p : RationalWords n) :
    rationalWordAugmentation p = p.coeff 1 := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change rationalWordEvaluation (fun _ => (0 : ℚ)) (MonoidAlgebra.single w 1) =
      (MonoidAlgebra.single w (1 : ℚ)).coeff 1
    rw [rationalWordEvaluation_single]
    cases hw : w.toList with
    | nil =>
      have hw1 : w = 1 := FreeMonoid.toList.injective hw
      subst w
      simp [MonoidAlgebra.coeff_single]
    | cons i l =>
      have hw1 : w ≠ 1 := by intro h; simp [h] at hw
      simp [MonoidAlgebra.coeff_single, hw1]
  | add p q hp hq =>
    simp only [map_add, hp, hq, MonoidAlgebra.coeff_add, Finsupp.add_apply]
  | smul r p hp =>
    simp only [map_smul, hp, MonoidAlgebra.coeff_smul, Finsupp.smul_apply]

theorem rationalWord_emptyCoeff_mul (p q : RationalWords n) :
    (p * q).coeff 1 = p.coeff 1 * q.coeff 1 := by
  rw [← rationalWordAugmentation_eq_coeff, map_mul,
    rationalWordAugmentation_eq_coeff, rationalWordAugmentation_eq_coeff]

end PolycyclicRecognition

end

end OAI
