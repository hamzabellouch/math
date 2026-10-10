import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordTensorConvolution

namespace OAI

/-! # The Dynkin projection identity for primitive rational words -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable {n : ℕ}

@[simp] theorem rationalWordDegree_one : rationalWordDegree (1 : RationalWords n) = 0 := by
  rw [MonoidAlgebra.one_def, rationalWordDegree_single]
  simp [FreeMonoid.length]

@[simp] theorem rationalWordAntipode_one :
    rationalWordAntipode (1 : RationalWords n) = 1 := by
  rw [MonoidAlgebra.one_def, rationalWordAntipode_single]
  simp [FreeMonoid.length, ← MonoidAlgebra.one_def]

theorem wordAntipodeConvolution_coproduct (p : RationalWords n) :
    wordAntipodeConvolution (rationalWordCoproduct p) =
      rationalWordAugmentation p • (1 : RationalWords n) := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change wordAntipodeConvolution (rationalWordCoproduct (MonoidAlgebra.single w 1)) =
      rationalWordAugmentation (MonoidAlgebra.single w 1) • (1 : RationalWords n)
    induction w using FreeMonoid.recOn with
    | one =>
      simp only [← MonoidAlgebra.one_def, map_one, one_smul]
      change wordAntipodeConvolution (1 ⊗ₜ[ℚ] 1) = 1
      simp
    | of_mul i w ih =>
      have h : MonoidAlgebra.single (FreeMonoid.of i * w) (1 : ℚ) =
          rationalWordLetter i * MonoidAlgebra.single w 1 := by
        simp [rationalWordLetter]
      rw [h, map_mul, rationalWordCoproduct_letter,
        wordAntipodeConvolution_letter_mul, ih]
      simp [rationalWordAugmentation, rationalWordLetter, rationalWordEvaluation_single,
        Algebra.mul_smul_comm]
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_smul]
  | smul r p hp =>
    simp only [map_smul, hp, smul_smul, smul_eq_mul]

theorem wordDegreeConvolution_coproduct (p : RationalWords n) :
    wordDegreeConvolution (rationalWordCoproduct p) =
      wordLieProjection rationalWordLetter p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change wordDegreeConvolution (rationalWordCoproduct (MonoidAlgebra.single w 1)) =
      wordLieProjection rationalWordLetter (MonoidAlgebra.single w 1)
    induction w using FreeMonoid.recOn with
    | one =>
      rw [← MonoidAlgebra.one_def, map_one]
      change wordDegreeConvolution (1 ⊗ₜ[ℚ] 1) = _
      rw [wordDegreeConvolution_tmul, rationalWordDegree_one, zero_mul,
        MonoidAlgebra.one_def, wordLieProjection_single]
      simp [wordRightLie]
    | of_mul i w ih =>
      have h : MonoidAlgebra.single (FreeMonoid.of i * w) (1 : ℚ) =
          rationalWordLetter i * MonoidAlgebra.single w 1 := by
        simp [rationalWordLetter]
      rw [h, map_mul, rationalWordCoproduct_letter,
        wordDegreeConvolution_letter_mul, wordAntipodeConvolution_coproduct, ih,
        wordLieProjection_letter_mul, rationalWordAugmentation_eq_coeff]
      simp only [Algebra.mul_smul_comm, mul_one]
      abel
  | add p q hp hq => simp only [map_add, hp, hq]
  | smul r p hp => simp only [map_smul, hp]

/-- Primitive words are sent to their degree derivative by the Dynkin projection. -/
theorem IsPrimitiveRationalWord.projection_eq_degree {p : RationalWords n}
    (hp : IsPrimitiveRationalWord p) :
    wordLieProjection rationalWordLetter p = rationalWordDegree p := by
  rw [← wordDegreeConvolution_coproduct, hp]
  simp

end PolycyclicRecognition

end

end OAI
