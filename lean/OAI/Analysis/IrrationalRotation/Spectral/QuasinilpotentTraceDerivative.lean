import OAI.Analysis.IrrationalRotation.Spectral.QuasinilpotentDeterminantReduction
import OAI.Analysis.IrrationalRotation.Operators.TracialNormSquareDerivative

namespace OAI

noncomputable section
namespace Invariant233

section BanachAlgebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem inverse_one_sub_smul_mul_moment_zero (φ : A →L[ℂ] ℂ) {T : A}
    (hT : NormQuasinilpotent T) (hmom : ∀ n : ℕ, 0 < n → φ (T ^ n) = 0)
    (z : ℂ) : φ (Ring.inverse (1 - z • T) * T) = 0 := by
  rw [hT.inverse_one_sub_smul z, ← (hT.summable_smul_pow z).tsum_mul_right T,
    φ.map_tsum ((hT.summable_smul_pow z).mul_right T)]
  have hz (n : ℕ) : φ ((z ^ n • T ^ n) * T) = 0 := by
    rw [smul_mul_assoc, ← pow_succ, map_smul, hmom (n + 1) (Nat.succ_pos n), smul_zero]
  simp only [hz, tsum_zero]

end BanachAlgebra

namespace TracialState
variable {A : Type*} [CStarAlgebra A]

theorem inverse_one_sub_smul_mul_eq_zero (τ : TracialState A) {T : A}
    (hT : NormQuasinilpotent T) (hmom : ∀ n : ℕ, 0 < n → τ (T ^ n) = 0)
    (z : ℂ) : τ (Ring.inverse (1 - z • T) * T) = 0 :=
  inverse_one_sub_smul_mul_moment_zero τ.toContinuousLinearMap hT hmom z

theorem inverse_one_sub_smul_mul_smul_eq_zero (τ : TracialState A) {T : A}
    (hT : NormQuasinilpotent T) (hmom : ∀ n : ℕ, 0 < n → τ (T ^ n) = 0)
    (z w : ℂ) : τ (Ring.inverse (1 - z • T) * (w • T)) = 0 := by
  rw [mul_smul_comm, map_smul, τ.inverse_one_sub_smul_mul_eq_zero hT hmom z,
    smul_zero]

theorem re_normalized_normSquare_differential_eq_zero (τ : TracialState A) {T : A}
    (hT : NormQuasinilpotent T) (hmom : ∀ n : ℕ, 0 < n → τ (T ^ n) = 0)
    (z w : ℂ) :
    (τ (Ring.inverse (star (1 - z • T) * (1 - z • T)) *
      (star (w • T) * (1 - z • T) + star (1 - z • T) * (w • T)))).re = 0 := by
  rw [τ.re_inverse_normSquare_differential _ _ (hT.isUnit_one_sub_smul z),
    τ.inverse_one_sub_smul_mul_smul_eq_zero hT hmom z w]
  simp

end TracialState
end Invariant233

end

end OAI
