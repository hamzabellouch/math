import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAdjointAction
import Mathlib.LinearAlgebra.Eigenspace.Zero

namespace OAI

/-! # The Jacobian of actual Cartan conjugation

The nilpotent residual exponential has determinant one. The scalar weight
factors multiply to one by the already proved trace balance. Consequently
conjugation on the nilpotent Cartan ideal preserves coordinate volume.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

/-- A unipotent real endomorphism has determinant one, including in dimension
zero. This uses its actual characteristic polynomial. -/
theorem det_eq_one_of_sub_one_nilpotent
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (F : Module.End ℝ V) (hF : _root_.IsNilpotent (F - 1)) : F.det = 1 := by
  have h := congrArg (Polynomial.eval (1 : ℝ)) hF.neg.charpoly_eq_X_pow_finrank
  rw [LinearMap.eval_charpoly] at h
  have he : (algebraMap ℝ (Module.End ℝ V) 1 - -(F - 1)) = F := by
    simp only [map_one, sub_neg_eq_add]
    abel
  rw [he] at h
  simpa using h

/-- Finite nilpotent exponential has unit determinant. -/
theorem det_nilpotent_exp
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [Module ℚ V] [IsScalarTower ℚ ℝ V]
    (A : Module.End ℝ V) (hA : _root_.IsNilpotent A) :
    LinearMap.det (_root_.IsNilpotent.exp A) = 1 :=
  det_eq_one_of_sub_one_nilpotent _ hA.isNilpotent_exp_sub_one

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra]
  {n : ℕ} (T : TriangularAdjoint L n)

/-- The nonsemisimple part of the actual Cartan action has Jacobian one. -/
theorem det_cartanIdealResidualAutomorphism (h : H) :
    LinearMap.det (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap = 1 := by
  let : Module ℚ (cartanRootIdeal H) := Module.compHom _ (algebraMap ℚ ℝ)
  exact det_nilpotent_exp (cartanIdealResidualDerivation T H h).toLinearMap
    ⟨finrank ℝ L, cartanIdealResidualDerivation_pow_eq_zero T H h⟩

namespace CartanWordModel

variable (M : CartanWordModel H)

/-- The diagonal scalar action has Jacobian given by the total word weight. -/
theorem det_idealWeightDilation (β : M.Bases) (h : H) :
    LinearMap.det (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap =
      Real.exp (∑ j, bracketWordExponent (fun i => M.weight i h) (β.val j)) := by
  let b := WordBasisSelections.basis M.letter M.wordList β
  let F := (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
  let v := fun j => Real.exp (bracketWordExponent (fun i => M.weight i h) (β.val j))
  have hb (j) : F (b j) = v j • b j := by
    have hh := M.idealWeightDilation_word T h (β.val j)
    have he := WordBasisSelections.eval_words M.letter M.wordList β j
    change evalBracketWord M.letter (β.val j) = b j at he
    rw [he] at hh
    exact hh
  have hm : LinearMap.toMatrix b b F = Matrix.diagonal v := by
    ext i j
    simp only [LinearMap.toMatrix_apply, hb, map_smul, Finsupp.smul_apply,
      Basis.repr_self, Finsupp.single_apply, smul_eq_mul, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [← LinearMap.det_toMatrix b, hm, Matrix.det_diagonal, Real.exp_sum]

include M in
/-- Unimodularity makes all word-basis scalar Jacobians equal to one. -/
theorem det_idealWeightDilation_eq_one
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0) (h : H) :
    LinearMap.det (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap = 1 := by
  let β : M.Bases := Classical.choice inferInstance
  rw [M.det_idealWeightDilation T β h]
  have ht := trace_cartan_word_basis H M.letter M.weight M.letter_root
    (WordBasisSelections.basis M.letter M.wordList β)
    (WordBasisSelections.words M.letter M.wordList β)
    (WordBasisSelections.eval_words M.letter M.wordList β) h
  have hz := trace_cartanRootIdeal_eq_zero T H hunimod h
  have hs : (∑ j, bracketWordExponent (fun i => M.weight i h) (β.val j)) = 0 := by
    rw [ht] at hz
    simp only [bracketWordExponent]
    rw [Finset.sum_comm]
    simpa only [Nat.cast_sum, Finset.sum_mul, WordBasisSelections.words] using hz
  rw [hs, Real.exp_zero]

include M in
/-- The full actual Cartan action, rather than only its scalar part, has
Jacobian one on the nilpotent ideal. -/
theorem det_idealAdjointAutomorphism_eq_one
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0) (h : H) :
    LinearMap.det (cartanIdealAdjointAutomorphism T H h).toLinearEquiv.toLinearMap = 1 := by
  change LinearMap.det ((cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap.comp
    (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap) = 1
  rw [LinearMap.det_comp, M.det_idealWeightDilation_eq_one T hunimod,
    det_cartanIdealResidualAutomorphism, mul_one]

end CartanWordModel
end PolycyclicRecognition

end

end OAI
