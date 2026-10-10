import OAI.Probability.SignedSweeps.TensorSupport
import OAI.Probability.SignedSweeps.WordTensorBasis

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

lemma positiveRoot_isometricConj (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (hA : A.IsPositive) :
    positiveRoot (isometricConj e A) (isometricConj_positive e hA) =
      isometricConj e (positiveRoot A hA) := by
  apply positive_square_root_unique _ _ (positiveRoot_positive _ _)
    (isometricConj_positive e (positiveRoot_positive A hA))
  rw [positiveRoot_square, ← isometricConj_mul, positiveRoot_square]

lemma supportInverseRoot_isometricConj (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (hA : A.IsPositive) :
    supportInverseRoot (isometricConj e A) (isometricConj_positive e hA) =
      isometricConj e (supportInverseRoot A hA) := by
  symm
  apply supportInverseRoot_unique _ _ (isometricConj_positive e hA)
  · rw [← isometricConj_mul, ← isometricConj_mul]
    congr 1
    exact (supportInverseRoot_commute A A hA rfl).symm
  · rw [positiveRoot_isometricConj e A hA, ← isometricConj_mul, ← isometricConj_mul, root_inverse_root]
  · rw [positiveRoot_isometricConj e A hA, ← isometricConj_mul, ← isometricConj_mul, inverse_root_inverse]

lemma spectralSupport_isometricConj (e : E ≃ₗᵢ[ℂ] F) (A : E →ₗ[ℂ] E) (hA : A.IsPositive) :
    spectralSupport (isometricConj e A) (isometricConj_positive e hA) =
      isometricConj e (spectralSupport A hA) := by
  rw [← supportInverseRoot_mul_root, supportInverseRoot_isometricConj e A hA,
    positiveRoot_isometricConj e A hA, ← isometricConj_mul, supportInverseRoot_mul_root]

end SignedSweeps
end

end OAI
