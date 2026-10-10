import OAI.GroupTheory.PolycyclicRecognition.Geometry.WordProjectionAdjoint
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteLieNorm

namespace OAI

/-! # The Dynkin projection on homogeneous bracket words -/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℚ A] {n : ℕ} (X : Fin n → A)

def rationalLieWord (w : FreeMagma (Fin n)) : RationalWords n :=
  evalBracketWord rationalWordLetter w

theorem rationalLieWord_eval (w : FreeMagma (Fin n)) :
    rationalWordEvaluation X (rationalLieWord w) = evalBracketWord X w := by
  induction w using FreeMagma.rec with
  | of i =>
    simp [rationalLieWord, evalBracketWord, rationalWordLetter,
      rationalWordEvaluation_single]
  | mul u v hu hv =>
    change rationalWordEvaluation X (rationalLieWord u * rationalLieWord v -
      rationalLieWord v * rationalLieWord u) = _
    rw [map_sub, map_mul, map_mul, hu, hv]
    rfl

theorem rationalLieWord_emptyCoeff (w : FreeMagma (Fin n)) :
    (rationalLieWord w).coeff 1 = 0 := by
  cases w with
  | of i =>
    simp [rationalLieWord, evalBracketWord, rationalWordLetter, MonoidAlgebra.coeff_single]
  | mul u v =>
    rw [← rationalWordAugmentation_eq_coeff]
    change rationalWordAugmentation (rationalLieWord u * rationalLieWord v -
      rationalLieWord v * rationalLieWord u) = 0
    rw [map_sub, map_mul, map_mul]
    exact sub_eq_zero.mpr (mul_comm _ _)

theorem rationalLieWord_adjoint (w : FreeMagma (Fin n)) :
    rationalWordAdjoint X (rationalLieWord w) = LieAlgebra.ad ℚ A (evalBracketWord X w) := by
  change rationalWordEvaluation (fun i => LieAlgebra.ad ℚ A (X i)) (rationalLieWord w) = _
  rw [rationalLieWord_eval]
  induction w using FreeMagma.rec with
  | of i => rfl
  | mul u v hu hv =>
    simp only [evalBracketWord, hu, hv, LieHom.map_lie]

theorem wordLieProjection_rationalLieWord (w : FreeMagma (Fin n)) :
    wordLieProjection X (rationalLieWord w) =
      (bracketWordLength w : ℚ) • evalBracketWord X w := by
  induction w using FreeMagma.rec with
  | of i =>
    simp [rationalLieWord, evalBracketWord, rationalWordLetter,
      wordLieProjection_single, wordRightLie, bracketWordLength]
  | mul u v hu hv =>
    change wordLieProjection X (rationalLieWord u * rationalLieWord v -
      rationalLieWord v * rationalLieWord u) = _
    rw [map_sub, wordLieProjection_mul X _ _ (rationalLieWord_emptyCoeff v),
      wordLieProjection_mul X _ _ (rationalLieWord_emptyCoeff u),
      rationalLieWord_adjoint, rationalLieWord_adjoint, hu, hv]
    change ⁅evalBracketWord X u, (bracketWordLength v : ℚ) • evalBracketWord X v⁆ -
      ⁅evalBracketWord X v, (bracketWordLength u : ℚ) • evalBracketWord X u⁆ = _
    rw [lie_smul, lie_smul]
    rw [sub_eq_add_neg, ← smul_neg, lie_skew]
    simp only [bracketWordLength, evalBracketWord, Nat.cast_add, add_smul]
    exact add_comm _ _

end PolycyclicRecognition

end

end OAI
