import Mathlib
import OAI.Analysis.WeakInfiniteness.FaithfulTensorNorm

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

namespace WeakPureInfiniteness

section FiniteTensorCompressions

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def compress (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (T : H →L[ℂ] H) : V →L[ℂ] V :=
  V.orthogonalProjectionOnto.comp (T.comp V.subtypeL)

lemma norm_compress_le (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (T : H →L[ℂ] H) : ‖compress V T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    ‖compress V T x‖ ≤ ‖T (x : H)‖ := V.norm_orthogonalProjectionOnto_apply_le _
    _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm _

lemma norm_tensorSum_compress_le {ι : Type*} (s : Finset ι)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (T : ι → H →L[ℂ] H) (S : ι → K →L[ℂ] K) :
    ‖∑ i ∈ s, TensorProduct.mapL (compress V (T i)) (S i)‖ ≤
      ‖∑ i ∈ s, TensorProduct.mapL (T i) (S i)‖ := by
  let P := V.orthogonalProjectionOnto.rTensor K
  let J := (V.subtypeₗᵢ.rTensor K).toContinuousLinearMap
  have hP : ‖P‖ ≤ 1 := by
    apply (ContinuousLinearMap.norm_rTensor_le K _).trans
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using V.norm_orthogonalProjectionOnto_apply_le x
  have hJ : ‖J‖ ≤ 1 := (V.subtypeₗᵢ.rTensor K).norm_toContinuousLinearMap_le
  have he : (∑ i ∈ s, TensorProduct.mapL (compress V (T i)) (S i)) =
      P.comp ((∑ i ∈ s, TensorProduct.mapL (T i) (S i)).comp J) := by
    apply ContinuousLinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul v k =>
      simp only [sum_apply, TensorProduct.mapL_tmul, ContinuousLinearMap.comp_apply,
        J, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.rTensor_apply,
        LinearMap.rTensor_tmul, P, map_sum, ContinuousLinearMap.rTensor_tmul]
      rfl
    | add z w hz hw => simp only [map_add, hz, hw]
  rw [he]
  calc
    _ ≤ ‖P‖ * (‖∑ i ∈ s, TensorProduct.mapL (T i) (S i)‖ * ‖J‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖∑ i ∈ s, TensorProduct.mapL (T i) (S i)‖ * 1) :=
      mul_le_mul hP (mul_le_mul_of_nonneg_left hJ (ContinuousLinearMap.opNorm_nonneg _))
        (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (ContinuousLinearMap.opNorm_nonneg J)) zero_le_one
    _ = _ := by rw [mul_one, one_mul]

lemma norm_tensorSum_le_of_finite_compressions {ι : Type*} [Finite ι] (s : Finset ι)
    (T : ι → H →L[ℂ] H) (S : ι → K →L[ℂ] K) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (V : Submodule ℂ H) [FiniteDimensional ℂ V],
      ‖∑ i ∈ s, TensorProduct.mapL (compress V (T i)) (S i)‖ ≤ C) :
    ‖∑ i ∈ s, TensorProduct.mapL (T i) (S i)‖ ≤ C := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro z
  obtain ⟨m, ξ, η, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  let V₀ := Submodule.span ℂ (Set.range ξ)
  let V₁ := Submodule.span ℂ (Set.range fun p : ι × Fin m => T p.1 (ξ p.2))
  let V := V₀ ⊔ V₁
  let : FiniteDimensional ℂ V₀ := FiniteDimensional.span_of_finite ℂ (Set.finite_range ξ)
  let : FiniteDimensional ℂ V₁ := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hξ (j : Fin m) : ξ j ∈ V :=
    (show V₀ ≤ V from le_sup_left) (Submodule.subset_span (Set.mem_range_self j))
  have hT (i : ι) (j : Fin m) : T i (ξ j) ∈ V :=
    (show V₁ ≤ V from le_sup_right) (Submodule.subset_span (Set.mem_range_self (i,j)))
  let v : V ⊗[ℂ] K := ∑ j, (⟨ξ j, hξ j⟩ : V) ⊗ₜ[ℂ] η j
  let J : (V ⊗[ℂ] K) →ₗᵢ[ℂ] (H ⊗[ℂ] K) := V.subtypeₗᵢ.rTensor K
  have hv : J v = ∑ j, ξ j ⊗ₜ[ℂ] η j := by
    simp only [J, v, map_sum, LinearIsometry.rTensor_apply, LinearMap.rTensor_tmul]
    rfl
  have he : J ((∑ i ∈ s, TensorProduct.mapL (compress V (T i)) (S i)) v) =
      (∑ i ∈ s, TensorProduct.mapL (T i) (S i)) (∑ j, ξ j ⊗ₜ[ℂ] η j) := by
    simp only [sum_apply, v, map_sum, TensorProduct.mapL_tmul,
      J, LinearIsometry.rTensor_apply, LinearMap.rTensor_tmul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    exact Submodule.starProjection_eq_self_iff.mpr (hT j i)
  rw [← he, J.norm_map, ← hv, J.norm_map]
  exact (ContinuousLinearMap.le_opNorm _ v).trans
    (mul_le_mul_of_nonneg_right (h V) (norm_nonneg v))

end FiniteTensorCompressions

section TensorNormIndependence

variable {H K L B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem tensor_norm_le_faithful {ι : Type*} [Finite ι] (s : Finset ι)
    (T : ι → H →L[ℂ] H) (a : ι → B)
    (φ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (ψ : B →⋆ₙₐ[ℂ] (L →L[ℂ] L))
    (hφ : Function.Injective φ) :
    ‖∑ i ∈ s, TensorProduct.mapL (T i) (ψ (a i))‖ ≤
      ‖∑ i ∈ s, TensorProduct.mapL (T i) (φ (a i))‖ := by
  apply norm_tensorSum_le_of_finite_compressions s T (fun i => ψ (a i))
    (ContinuousLinearMap.opNorm_nonneg (∑ i ∈ s, TensorProduct.mapL (T i) (φ (a i))))
  intro V hV
  exact (tensor_norm_le_faithful_finite_left s (stdOrthonormalBasis ℂ V)
    (fun i => compress V (T i)) a φ ψ hφ).trans
      (norm_tensorSum_compress_le s V T (fun i => φ (a i)))

end TensorNormIndependence

end WeakPureInfiniteness
end

end OAI
