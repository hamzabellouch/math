import OAI.Analysis.WeakInfiniteness.TensorNorm

namespace OAI

/-! Algebraic faithfulness of the spatial product of two faithful
representations. Finite coefficient separation uses ordinary linear duals;
no simplicity or nuclearity hypothesis occurs. -/

noncomputable section
open scoped TensorProduct BigOperators

namespace WeakPureInfiniteness

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem spatial_sum_coefficients_zero {I : Type*} [Fintype I]
    (a : I → H →L[ℂ] H) (b : I → K →L[ℂ] K) (hb : LinearIndependent ℂ b)
    (h : ∑ i, TensorProduct.mapL (a i) (b i) = 0) : ∀ i, a i = 0 := by
  classical
  have hcoeff (x : H) (ℓ : Module.Dual ℂ H) : ∀ i, ℓ (a i x) = 0 := by
    apply Fintype.linearIndependent_iff.mp hb
    apply ContinuousLinearMap.ext
    intro y
    have hv : ∑ i, (a i x) ⊗ₜ[ℂ] (b i y) = 0 := by
      have hv := congrArg (fun T : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K => T (x ⊗ₜ[ℂ] y)) h
      simpa only [sum_apply, TensorProduct.mapL_tmul, zero_apply] using hv
    let S : H ⊗[ℂ] K →ₗ[ℂ] K :=
      (TensorProduct.lid ℂ K).toLinearMap.comp (TensorProduct.map ℓ (LinearMap.id : K →ₗ[ℂ] K))
    have hs := congrArg S hv
    simpa [S] using hs
  intro i
  apply ContinuousLinearMap.ext
  intro x
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro ℓ
  exact hcoeff x ℓ i

def spatialOperatorBilinear : (H →L[ℂ] H) →ₗ[ℂ]
    (K →L[ℂ] K) →ₗ[ℂ] (H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) where
  toFun a :=
    { toFun := fun b => TensorProduct.mapL a b
      map_add' := TensorProduct.mapL_add_right a
      map_smul' := fun c b => TensorProduct.mapL_smul_right c a b }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    exact TensorProduct.mapL_add_left a b c
  map_smul' c a := by
    apply LinearMap.ext
    intro b
    exact TensorProduct.mapL_smul_left c a b

def spatialOperatorTensor : (H →L[ℂ] H) ⊗[ℂ] (K →L[ℂ] K) →ₗ[ℂ]
    (H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) := TensorProduct.lift spatialOperatorBilinear

theorem spatialOperatorTensor_injective : Function.Injective (spatialOperatorTensor (H := H) (K := K)) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let b := Module.Free.chooseBasis ℂ (K →L[ℂ] K)
  obtain ⟨a, rfl⟩ := TensorProduct.eq_repr_basis_right b z
  have h : ∑ i : ↥a.support, TensorProduct.mapL (a i.val) (b i.val) = 0 := by
    have he : ∑ i ∈ a.support, TensorProduct.mapL (a i) (b i) = 0 := by
      simpa only [Finsupp.sum, map_sum, TensorProduct.lift.tmul,
        spatialOperatorTensor, spatialOperatorBilinear, LinearMap.coe_mk,
        AddHom.coe_mk] using hz
    exact (Finset.sum_coe_sort a.support (fun i => TensorProduct.mapL (a i) (b i))).trans he
  have hi := spatial_sum_coefficients_zero (fun i : ↥a.support => a i.val)
    (fun i : ↥a.support => b i.val) (b.linearIndependent.comp Subtype.val Subtype.val_injective) h
  apply Finset.sum_eq_zero
  intro i hi'
  change a i ⊗ₜ[ℂ] b i = 0
  rw [hi ⟨i, hi'⟩, TensorProduct.zero_tmul]

/-- A norm-zero spatial finite sum vanishes as an algebraic tensor of
operators. Stating this over the Hilbert spaces keeps all operator instances
fixed before applying it to bundled representations. -/
theorem operator_tensor_sum_eq_zero_of_norm_le {I : Type*} [Fintype I]
    (a : I → H →L[ℂ] H) (b : I → K →L[ℂ] K)
    (hn : ‖∑ i, TensorProduct.mapL (a i) (b i)‖ ≤ 0) :
    (∑ i, a i ⊗ₜ[ℂ] b i) = 0 := by
  apply spatialOperatorTensor_injective
  rw [map_zero]
  have hs : (∑ i, TensorProduct.mapL (a i) (b i)) = 0 :=
    (ContinuousLinearMap.opNorm_zero_iff _).mp (le_antisymm hn (norm_nonneg _))
  simpa only [map_sum, spatialOperatorTensor, TensorProduct.lift.tmul,
    spatialOperatorBilinear, LinearMap.coe_mk, AddHom.coe_mk] using hs

end WeakPureInfiniteness

end

end OAI
