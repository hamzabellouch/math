import OAI.GroupTheory.PolycyclicRecognition.Algebra.MonoidCoefficientLinear
import OAI.GroupTheory.PolycyclicRecognition.Algebra.MonoidTensorCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalWordCoproduct

namespace OAI

/-! # Coefficient extraction commutes with the primitive word coproduct -/

noncomputable section
namespace PolycyclicRecognition

variable (R : Type*) [CommRing R] (n : ℕ)

def pairedWordCoproduct : MonoidAlgebra R (FreeMonoid (Fin n)) →ₐ[R]
    MonoidAlgebra R (FreeMonoid (Fin n) × FreeMonoid (Fin n)) :=
  MonoidAlgebra.lift _ _ _ (FreeMonoid.lift (fun i =>
    MonoidAlgebra.single (FreeMonoid.of i, 1) 1 +
      MonoidAlgebra.single (1, FreeMonoid.of i) 1))

theorem pairedWordCoproduct_letter (i : Fin n) :
    pairedWordCoproduct R n (MonoidAlgebra.single (FreeMonoid.of i) 1) =
      MonoidAlgebra.single (FreeMonoid.of i, 1) 1 +
        MonoidAlgebra.single (1, FreeMonoid.of i) 1 := by
  simp [pairedWordCoproduct, MonoidAlgebra.lift_single, FreeMonoid.lift_apply]

variable {R n} [Module ℚ R]

theorem coefficientLinear_pairedWordCoproduct (f : R →ₗ[ℚ] ℚ)
    (p : MonoidAlgebra R (FreeMonoid (Fin n))) :
    monoidCoefficientLinear f (pairedWordCoproduct R n p) =
      pairedWordCoproduct ℚ n (monoidCoefficientLinear f p) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single w r =>
    rw [monoidCoefficientLinear_single]
    induction w using FreeMonoid.recOn with
    | one =>
      simp [pairedWordCoproduct, MonoidAlgebra.lift_single, FreeMonoid.lift_apply,
        MonoidAlgebra.one_def, smul_eq_mul]
    | of_mul i w ih =>
      have hR : MonoidAlgebra.single (FreeMonoid.of i * w) r =
          MonoidAlgebra.single (FreeMonoid.of i) (1 : R) * MonoidAlgebra.single w r := by simp
      have hQ : MonoidAlgebra.single (FreeMonoid.of i * w) (f r) =
          MonoidAlgebra.single (FreeMonoid.of i) (1 : ℚ) * MonoidAlgebra.single w (f r) := by simp
      rw [hR, hQ, map_mul (pairedWordCoproduct R n), map_mul (pairedWordCoproduct ℚ n),
        pairedWordCoproduct_letter, pairedWordCoproduct_letter]
      simp only [add_mul, map_add, monoidCoefficientLinear_single_mul, ih]

theorem pairedWordCoproduct_eq_rational (p : RationalWords n) :
    pairedWordCoproduct ℚ n p =
      monoidTensorCoordinates ℚ (FreeMonoid (Fin n)) (FreeMonoid (Fin n))
        (rationalWordCoproduct p) := by
  change pairedWordCoproduct ℚ n p =
    ((monoidTensorCoordinates ℚ (FreeMonoid (Fin n)) (FreeMonoid (Fin n))).comp
      rationalWordCoproduct) p
  apply congrArg (fun F : RationalWords n →ₐ[ℚ] _ => F p)
  apply MonoidAlgebra.algHom_ext'
  · apply FreeMonoid.hom_eq
    intro i
    change pairedWordCoproduct ℚ n (rationalWordLetter i) =
      monoidTensorCoordinates ℚ _ _ (rationalWordCoproduct (rationalWordLetter i))
    rw [rationalWordCoproduct_letter, map_add]
    simp only [rationalWordLetter, pairedWordCoproduct_letter, MonoidAlgebra.one_def,
      monoidTensorCoordinates_single, one_mul]
  · exact Subsingleton.elim _ _

end PolycyclicRecognition

end

end OAI
