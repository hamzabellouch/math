import OAI.Probability.SignedSweeps.SupportInverse

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma positive_square_root_unique (A B : E →ₗ[ℂ] E)
    (hA : A.IsPositive) (hB : B.IsPositive) (h : A * A = B * B) : A = B := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have ha : (0 : E →L[ℂ] E) ≤ A.toContinuousLinearMap :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr hA
  have hb : (0 : E →L[ℂ] E) ≤ B.toContinuousLinearMap :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr hB
  have hh : A.toContinuousLinearMap * A.toContinuousLinearMap =
      B.toContinuousLinearMap * B.toContinuousLinearMap :=
    congrArg LinearMap.toContinuousLinearMap h
  have hs := congrArg CFC.sqrt hh
  rw [CFC.sqrt_mul_self _ ha, CFC.sqrt_mul_self _ hb] at hs
  exact congrArg ContinuousLinearMap.toLinearMap hs

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

lemma tensor_map_positive (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F)
    (hA : A.IsPositive) (hB : B.IsPositive) : (TensorProduct.map A B).IsPositive := by
  have hp := adjoint_mul_positive (TensorProduct.map (positiveRoot A hA) (positiveRoot B hB))
  rw [positiveSquare, TensorProduct.adjoint_map, (positiveRoot_positive _ hA).isSymmetric.adjoint_eq,
    (positiveRoot_positive _ hB).isSymmetric.adjoint_eq, ← TensorProduct.map_mul,
    positiveRoot_square, positiveRoot_square] at hp
  exact hp

lemma positiveRoot_tensor (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F)
    (hA : A.IsPositive) (hB : B.IsPositive) :
    positiveRoot (TensorProduct.map A B) (tensor_map_positive A B hA hB) =
      TensorProduct.map (positiveRoot A hA) (positiveRoot B hB) := by
  apply positive_square_root_unique _ _ (positiveRoot_positive _ _)
    (tensor_map_positive _ _ (positiveRoot_positive _ _) (positiveRoot_positive _ _))
  rw [positiveRoot_square, ← TensorProduct.map_mul, positiveRoot_square, positiveRoot_square]

lemma tensor_map_norm_le (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) :
    ‖(TensorProduct.map A B).toContinuousLinearMap‖ ≤
      ‖A.toContinuousLinearMap‖ * ‖B.toContinuousLinearMap‖ := by
  have hh : (TensorProduct.map A B).toContinuousLinearMap =
      TensorProduct.mapL A.toContinuousLinearMap B.toContinuousLinearMap := by
    ext x
    simp only [TensorProduct.mapL_apply, LinearMap.coe_toContinuousLinearMap']
    rfl
  rw [hh]
  exact TensorProduct.norm_mapL_le A.toContinuousLinearMap B.toContinuousLinearMap

lemma tensor_map_norm_sq_le (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) :
    ‖(TensorProduct.map A B).toContinuousLinearMap‖ ^ 2 ≤
      ‖A.toContinuousLinearMap‖ ^ 2 * ‖B.toContinuousLinearMap‖ ^ 2 := by
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (TensorProduct.map A B).toContinuousLinearMap)
    (tensor_map_norm_le A B) 2

end SignedSweeps
end

end OAI
