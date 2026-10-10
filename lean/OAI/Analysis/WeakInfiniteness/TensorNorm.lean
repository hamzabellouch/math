import Mathlib
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorBound

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped TensorProduct

universe u v w z

section Hilbert

variable {E : Type u} {F : Type v} {G : Type w} {H : Type z}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma norm_tensorProduct_mapL (f : E →L[ℂ] F) (g : G →L[ℂ] H) :
    ‖TensorProduct.mapL f g‖=‖f‖*‖g‖ := by
  apply le_antisymm (TensorProduct.norm_mapL_le f g)
  let N := ‖TensorProduct.mapL f g‖
  have hxy (x : E) (y : G) : ‖f x‖*‖g y‖ ≤ (N*‖x‖)*‖y‖ := by
    have h := (TensorProduct.mapL f g).le_opNorm (x ⊗ₜ[ℂ] y)
    simpa only [TensorProduct.mapL_tmul,TensorProduct.norm_tmul,mul_assoc] using h
  have hx (x : E) : ‖f x‖*‖g‖ ≤ N*‖x‖ := by
    have h : ‖(‖f x‖:ℂ) • g‖ ≤ N*‖x‖ := by
      refine ContinuousLinearMap.opNorm_le_bound ((‖f x‖:ℂ) • g)
        (show 0≤N*‖x‖ from mul_nonneg (norm_nonneg (TensorProduct.mapL f g)) (norm_nonneg _)) ?_
      intro y
      simpa only [smul_apply,norm_smul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hxy x y
    simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using h
  have h : ‖(‖g‖:ℂ) • f‖ ≤ N := by
    refine ContinuousLinearMap.opNorm_le_bound ((‖g‖:ℂ) • f) (show 0≤N from norm_nonneg (TensorProduct.mapL f g)) ?_
    intro x
    simpa only [smul_apply,norm_smul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),mul_comm ‖g‖] using hx x
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _),mul_comm ‖g‖] using h

end Hilbert

section CrossNorm

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma norm_minimalElementary (a : A) (b : B) : ‖minimalElementary a b‖=‖a‖*‖b‖ := by
  apply le_antisymm (norm_spatialElementary_le a b)
  obtain ⟨H,π,hπ⟩ := exists_faithful_representation A
  obtain ⟨K,ρ,hρ⟩ := exists_faithful_representation B
  have hn : ‖TensorProduct.mapL (π a) (ρ b)‖ ≤ ‖minimalElementary a b‖ := by
    change ‖TensorProduct.mapL (π a) (ρ b)‖ ≤ ‖spatialElementary a b‖
    simpa using norm_tensorSum_le_spatial_any ({()} : Finset Unit) (fun _ : Unit => a)
      (fun _ : Unit => b) π ρ
  rw [norm_tensorProduct_mapL] at hn
  have ha : ‖π a‖=‖a‖ := (NonUnitalStarAlgHom.isometry π hπ).norm_map_of_map_zero (map_zero π) a
  have hb : ‖ρ b‖=‖b‖ := (NonUnitalStarAlgHom.isometry ρ hρ).norm_map_of_map_zero (map_zero ρ) b
  rwa [ha,hb] at hn

end CrossNorm

end

end WeakPureInfiniteness
end

end OAI
