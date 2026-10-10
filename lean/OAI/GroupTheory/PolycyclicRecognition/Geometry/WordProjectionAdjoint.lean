import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalWordEvaluation
import Mathlib.Algebra.Lie.OfAssociative

namespace OAI

/-! # The adjoint action on the right-nested word projection -/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℚ A] {n : ℕ} (X : Fin n → A)

def rationalWordAdjoint : RationalWords n →ₐ[ℚ] Module.End ℚ A :=
  rationalWordEvaluation (fun i => LieAlgebra.ad ℚ A (X i))

theorem wordLieProjection_word_mul (w : FreeMonoid (Fin n)) (q : RationalWords n)
    (hq : q.coeff 1 = 0) :
    wordLieProjection X (MonoidAlgebra.single w 1 * q) =
      FreeMonoid.lift (fun i => LieAlgebra.ad ℚ A (X i)) w (wordLieProjection X q) := by
  induction w using FreeMonoid.recOn with
  | one => simp [← MonoidAlgebra.one_def]
  | of_mul i w ih =>
    have heq : MonoidAlgebra.single (FreeMonoid.of i * w) (1 : ℚ) =
        rationalWordLetter i * MonoidAlgebra.single w 1 := by
      rw [rationalWordLetter, MonoidAlgebra.single_mul_single, one_mul]
    rw [heq, mul_assoc, wordLieProjection_letter_mul, rationalWord_emptyCoeff_mul,
      hq, mul_zero, zero_smul, add_zero, ih, map_mul]
    rw [show FreeMonoid.lift (fun i => LieAlgebra.ad ℚ A (X i)) (FreeMonoid.of i) =
      LieAlgebra.ad ℚ A (X i) from rfl]
    rfl

theorem wordLieProjection_mul (p q : RationalWords n) (hq : q.coeff 1 = 0) :
    wordLieProjection X (p * q) = rationalWordAdjoint X p (wordLieProjection X q) := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change wordLieProjection X (MonoidAlgebra.single w 1 * q) = _
    rw [wordLieProjection_word_mul X w q hq]
    change _ = rationalWordEvaluation (fun i => LieAlgebra.ad ℚ A (X i))
      (MonoidAlgebra.single w 1) (wordLieProjection X q)
    rw [rationalWordEvaluation_single, one_smul, ← FreeMonoid.lift_apply]
  | add p r hp hr => simp only [add_mul, map_add, hp, hr, LinearMap.add_apply]
  | smul r p hp => simp only [smul_mul_assoc, map_smul, hp, LinearMap.smul_apply]

end PolycyclicRecognition

end

end OAI
