import OAI.GroupTheory.PolycyclicRecognition.Geometry.RationalLieWordProjection
import Mathlib.RingTheory.TensorProduct.Basic

namespace OAI

/-! # The primitive coproduct on rational words -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable {n : ℕ}

def rationalWordCoproduct : RationalWords n →ₐ[ℚ] RationalWords n ⊗[ℚ] RationalWords n :=
  rationalWordEvaluation (fun i =>
    rationalWordLetter i ⊗ₜ[ℚ] (1 : RationalWords n) +
      (1 : RationalWords n) ⊗ₜ[ℚ] rationalWordLetter i)

def IsPrimitiveRationalWord (p : RationalWords n) : Prop :=
  rationalWordCoproduct p = p ⊗ₜ[ℚ] (1 : RationalWords n) + (1 : RationalWords n) ⊗ₜ[ℚ] p

theorem rationalWordCoproduct_letter (i : Fin n) :
    IsPrimitiveRationalWord (rationalWordLetter i) := by
  unfold IsPrimitiveRationalWord rationalWordCoproduct rationalWordLetter
  rw [rationalWordEvaluation_single]
  simp

theorem IsPrimitiveRationalWord.commutator {p q : RationalWords n}
    (hp : IsPrimitiveRationalWord p) (hq : IsPrimitiveRationalWord q) :
    IsPrimitiveRationalWord (p * q - q * p) := by
  unfold IsPrimitiveRationalWord at hp hq ⊢
  rw [map_sub, map_mul, map_mul, hp, hq]
  simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul, sub_tmul, tmul_sub]
  abel

theorem rationalLieWord_primitive (w : FreeMagma (Fin n)) :
    IsPrimitiveRationalWord (rationalLieWord w) := by
  induction w using FreeMagma.rec with
  | of i => exact rationalWordCoproduct_letter i
  | mul u v hu hv => exact hu.commutator hv

end PolycyclicRecognition

end

end OAI
