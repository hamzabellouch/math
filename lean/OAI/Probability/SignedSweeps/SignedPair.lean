import OAI.Probability.SignedSweeps.PairCentral
import OAI.Probability.SignedSweeps.SignedWords

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) signedPairWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) signedPairSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

def wordPhaseDiagonal {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) where
  toFun f := WithLp.toLp 2 (fun w => wordPhase g w * f w)
  map_add' f h := by ext w; exact mul_add _ _ _
  map_smul' c f := by ext w; exact mul_left_comm _ _ _

lemma signedWordRepresentation_eq {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    signedWordRepresentation p C g = wordPhaseDiagonal g * wordRepresentation p (C ⊕ C) g := rfl

lemma wordPhaseDiagonal_matrix {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    wordMatrixEquiv p (C ⊕ C) (wordPhaseDiagonal g) = Matrix.diagonal (wordPhase g) := by
  ext w z
  simp only [wordMatrixEquiv, LinearMap.toMatrixOrthonormal_apply_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  change wordPhase g w * (EuclideanSpace.single z (1 : ℂ)) w = _
  simp only [PiLp.single_apply, Matrix.diagonal_apply]
  split_ifs with hw
  · subst z; simp
  · simp

lemma pairTypeProjection_phase_commute {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (g : SymmetricGroup p) :
    pairTypeProjection h α β C * wordPhaseDiagonal g =
      wordPhaseDiagonal g * pairTypeProjection h α β C := by
  apply (wordMatrixEquiv p (C ⊕ C)).injective
  change wordMatrixEquiv p (C ⊕ C) (_ * _) = wordMatrixEquiv p (C ⊕ C) (_ * _)
  rw [map_mul, map_mul, wordPhaseDiagonal_matrix]
  ext w z
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hp : wordEvenSites w = wordEvenSites z
  · rw [wordPhase_eq_of_parity g w z hp, mul_comm]
  · rw [pairTypeProjection_parity_off h α β w z hp, zero_mul, mul_zero]

theorem pairTypeProjection_signed_commute {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (α : Partition u) (β : Partition v) (g : SymmetricGroup p) :
    pairTypeProjection h α β C * signedWordRepresentation p C g =
      signedWordRepresentation p C g * pairTypeProjection h α β C := by
  rw [signedWordRepresentation_eq, ← mul_assoc,
    pairTypeProjection_phase_commute h α β g, mul_assoc,
    pairTypeProjection_perm_commute h α β g, ← mul_assoc]

end SignedSweeps
end

end OAI
