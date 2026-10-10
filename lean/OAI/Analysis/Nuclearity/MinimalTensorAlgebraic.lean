import OAI.Analysis.Nuclearity.UnitalMinimalTensor
import OAI.Analysis.Nuclearity.SpatialTensorFaithful
import OAI.Analysis.TracialSplitting.GNSRepresentations

namespace OAI

/-! The algebraic tensor product embeds faithfully and densely in the
minimal C*-completion. -/

noncomputable section
open scoped TensorProduct BigOperators

namespace WeakPureInfiniteness.UnitalMinimalTensor

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

local instance algebraicTensorUnital : CStarAlgebra (MinimalTensor A B) :=
  minimalTensorUnitalStructure A B

def algebraicMap : A ⊗[ℂ] B →⋆ₐ[ℂ] MinimalTensor A B :=
  Pureness.commutingStarTensorHom (leftEmbedding A B) (rightEmbedding A B) (legs_commute A B)

@[simp] theorem algebraicMap_tmul (a : A) (b : B) :
    algebraicMap (a ⊗ₜ[ℂ] b) = minimalElementary a b := legs_mul A B a b

theorem algebraicMap_injective : Function.Injective (algebraicMap (A := A) (B := B)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨H, π, hπ⟩ := exists_faithful_representation A
  obtain ⟨K, ρ, hρ⟩ := exists_faithful_representation B
  let p : A →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := π, map_add' := map_add π, map_smul' := map_smul π }
  let q : B →ₗ[ℂ] (K →L[ℂ] K) :=
    { toFun := ρ, map_add' := map_add ρ, map_smul' := map_smul ρ }
  have hmap : Function.Injective (TensorProduct.map p q) :=
    TensorProduct.map_injective_of_flat_flat p q hπ hρ
  apply hmap
  rw [map_zero]
  obtain ⟨n, a, b, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  have hz' : (∑ i : Fin n, minimalElementary (a i) (b i)) = 0 := by
    simpa only [map_sum, algebraicMap_tmul] using hz
  have hn : ‖∑ i : Fin n, TensorProduct.mapL (π (a i)) (ρ (b i))‖ ≤
      ‖∑ i : Fin n, minimalElementary (a i) (b i)‖ := by
    change _ ≤ ‖(minimalTensorSubalgebra A B).subtype
      (∑ i : Fin n, minimalElementary (a i) (b i))‖
    simp only [map_sum]
    change ‖∑ i : Fin n, TensorProduct.mapL (π (a i)) (ρ (b i))‖ ≤
      ‖∑ i : Fin n, spatialElementary (a i) (b i)‖
    exact norm_tensorSum_le_spatial_any Finset.univ a b π ρ
  rw [hz', norm_zero] at hn
  simpa only [map_sum, TensorProduct.map_tmul, p, q, LinearMap.coe_mk, AddHom.coe_mk] using
    operator_tensor_sum_eq_zero_of_norm_le (fun i => π (a i)) (fun i => ρ (b i)) hn

theorem algebraicMap_dense : DenseRange (algebraicMap (A := A) (B := B)) := by
  let S := (algebraicMap (A := A) (B := B)).toLinearMap.range
  have hs : S.topologicalClosure = ⊤ := by
    apply minimal_elementary_span_dense _ S.isClosed_topologicalClosure
    intro a b
    apply S.le_topologicalClosure
    exact ⟨a ⊗ₜ[ℂ] b, algebraicMap_tmul a b⟩
  intro x
  change x ∈ S.topologicalClosure
  rw [hs]
  trivial

end WeakPureInfiniteness.UnitalMinimalTensor

end

end OAI
