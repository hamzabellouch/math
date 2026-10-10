import OAI.Analysis.OperatorAlgebra.DensitySpatialRepresentation

namespace OAI

/-! The left spatial vector functional of a density root is the original
finite positive functional. The finite-dimensional computation is the
trace identity used before passage to a common finite support. -/

noncomputable section
open scoped InnerProductSpace TensorProduct ComplexOrder

namespace WeakPureInfiniteness

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma finiteOperatorTensor_left [FiniteDimensional ℂ H] (A T : H →L[ℂ] H) :
    TensorProduct.mapL A (ContinuousLinearMap.id ℂ (StrongDual ℂ H))
      (NuclearUltrapower.finiteOperatorTensor T) =
        NuclearUltrapower.finiteOperatorTensor (A * T) := by
  classical
  simp only [NuclearUltrapower.finiteOperatorTensor, map_sum, TensorProduct.mapL_tmul,
    ContinuousLinearMap.id_apply, mul_apply_eq_comp]

lemma densityRoot_eq_finiteOperatorTensor [FiniteDimensional ℂ H] (z : E ⊗[ℂ] H) :
    NuclearUltrapower.densityRoot z =
      (NuclearUltrapower.finiteOperatorTensor (CFC.sqrt (NuclearUltrapower.reducedDensity z)) :
        NuclearUltrapower.HilbertSchmidt H) := by
  apply NuclearUltrapower.hsOperator_injective
  rw [NuclearUltrapower.hsOperator_densityRoot, NuclearUltrapower.hsOperator_coe,
    NuclearUltrapower.tensorOperator_finiteOperatorTensor]

lemma densityRoot_left_quadratic_finite [FiniteDimensional ℂ H]
    (z : E ⊗[ℂ] H) (A : H →L[ℂ] H) :
    inner ℂ (NuclearUltrapower.densityRoot z)
      (densityLeftRepresentation A (NuclearUltrapower.densityRoot z)) =
        (finiteTensorDensity z).val A := by
  rw [densityRoot_eq_finiteOperatorTensor, densityLeft_coe,
    UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := H ⊗[ℂ] StrongDual ℂ H), finiteOperatorTensor_left,
    NuclearUltrapower.finiteOperatorTensor_inner,
    (CFC.sqrt_nonneg (NuclearUltrapower.reducedDensity z)).isSelfAdjoint.star_eq]
  let r := CFC.sqrt (NuclearUltrapower.reducedDensity z)
  change LinearMap.trace ℂ H ((r * (A * r)).toLinearMap) = _
  have hc : LinearMap.trace ℂ H ((r * (A * r)).toLinearMap) =
      LinearMap.trace ℂ H (((A * r) * r).toLinearMap) :=
    LinearMap.trace_mul_comm ℂ r.toLinearMap (A * r).toLinearMap
  rw [hc, mul_assoc]
  have hr : r * r = NuclearUltrapower.reducedDensity z :=
    CFC.sqrt_mul_sqrt_self _ (NuclearUltrapower.reducedDensity_nonneg z)
  rw [hr, NuclearUltrapower.trace_reducedDensity, finiteTensorDensity_apply]

end WeakPureInfiniteness

end

end OAI
