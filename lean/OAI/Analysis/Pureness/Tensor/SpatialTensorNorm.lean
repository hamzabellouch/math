import OAI.Analysis.Pureness.Comparison.SpatialTensorOperators

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem spatialTensorOp_norm (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    ‖spatialTensorOp S T‖ = ‖S‖*‖T‖ := by
  apply le_antisymm (spatialTensorOp_norm_le S T)
  let C := ‖spatialTensorOp S T‖
  have hxy (x : H) (y : K) : ‖S x‖*‖T y‖ ≤ C*(‖x‖*‖y‖) := by
    have h := (spatialTensorOp S T).le_opNorm (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K)
    simpa only [spatialTensorOp_coe,TensorProduct.mapL_tmul,
      UniformSpace.Completion.norm_coe,TensorProduct.norm_tmul] using h
  have hy (y : K) : ‖S‖*‖T y‖ ≤ C*‖y‖ := by
    have h := ContinuousLinearMap.opNorm_le_bound ((‖T y‖ : ℂ) • S)
      (mul_nonneg (norm_nonneg (spatialTensorOp S T)) (norm_nonneg y)) (fun x => ?_)
    · simpa [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg,mul_comm] using h
    · simp only [smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg (T y))]
      calc
        ‖T y‖*‖S x‖ = ‖S x‖*‖T y‖ := mul_comm _ _
        _ ≤ C*(‖x‖*‖y‖) := hxy x y
        _ = (C*‖y‖)*‖x‖ := by ring
  have h := ContinuousLinearMap.opNorm_le_bound ((‖S‖ : ℂ) • T)
    (norm_nonneg (spatialTensorOp S T)) (fun y => ?_)
  · simpa [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg] using h
  · simpa only [smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg S)] using hy y
end CuntzPureness

end

end OAI
