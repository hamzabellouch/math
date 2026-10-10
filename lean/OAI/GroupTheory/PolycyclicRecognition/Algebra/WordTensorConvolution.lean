import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalWordCoproduct
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalWordOperators
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # The antipode and degree convolutions for rational words -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable {n : ℕ}

def wordAntipodeConvolution :
    RationalWords n ⊗[ℚ] RationalWords n →ₗ[ℚ] RationalWords n :=
  (LinearMap.mul' ℚ (RationalWords n)).comp
    (TensorProduct.map LinearMap.id rationalWordAntipode)

def wordDegreeConvolution :
    RationalWords n ⊗[ℚ] RationalWords n →ₗ[ℚ] RationalWords n :=
  (LinearMap.mul' ℚ (RationalWords n)).comp
    (TensorProduct.map rationalWordDegree rationalWordAntipode)

@[simp] theorem wordAntipodeConvolution_tmul (p q : RationalWords n) :
    wordAntipodeConvolution (p ⊗ₜ[ℚ] q) = p * rationalWordAntipode q := rfl

@[simp] theorem wordDegreeConvolution_tmul (p q : RationalWords n) :
    wordDegreeConvolution (p ⊗ₜ[ℚ] q) =
      rationalWordDegree p * rationalWordAntipode q := rfl

theorem wordAntipodeConvolution_letter_mul (i : Fin n)
    (u : RationalWords n ⊗[ℚ] RationalWords n) :
    wordAntipodeConvolution
        ((rationalWordLetter i ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] rationalWordLetter i) * u) =
      rationalWordLetter i * wordAntipodeConvolution u -
        wordAntipodeConvolution u * rationalWordLetter i := by
  induction u using TensorProduct.inductionOn with
  | tmul p q =>
    simp only [add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_add,
      wordAntipodeConvolution_tmul, rationalWordAntipode_letter_mul]
    noncomm_ring
  | add u v hu hv =>
    rw [mul_add, map_add, hu, hv]
    simp only [map_add, mul_add, add_mul]
    abel

theorem wordDegreeConvolution_letter_mul (i : Fin n)
    (u : RationalWords n ⊗[ℚ] RationalWords n) :
    wordDegreeConvolution
        ((rationalWordLetter i ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] rationalWordLetter i) * u) =
      rationalWordLetter i * wordAntipodeConvolution u +
        rationalWordLetter i * wordDegreeConvolution u -
        wordDegreeConvolution u * rationalWordLetter i := by
  induction u using TensorProduct.inductionOn with
  | tmul p q =>
    simp only [add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_add,
      wordAntipodeConvolution_tmul, wordDegreeConvolution_tmul,
      rationalWordDegree_letter_mul, rationalWordAntipode_letter_mul]
    noncomm_ring
  | add u v hu hv =>
    rw [mul_add, map_add, hu, hv]
    simp only [map_add, mul_add, add_mul]
    abel

end PolycyclicRecognition

end

end OAI
