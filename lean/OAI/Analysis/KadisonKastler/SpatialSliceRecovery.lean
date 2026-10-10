import OAI.Analysis.KadisonKastler.SpatialRightSlice
import OAI.Analysis.KadisonKastler.PublishedCentralDecomposition

namespace OAI

/-! # Recovering the first tensor leg from scalar opposite slices

Polarization proves the relative-commutant identity needed for the fixed
product factor. No spatial tensor commutation theorem is added as an input.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Pure-tensor inner products determine a vector in the completed tensor product. -/
theorem spatialTensor_vector_ext {v w : SpatialHilbert H K}
    (h : ∀ (x : H) (η : K),
      inner ℂ (((x ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : SpatialHilbert H K)) v =
      inner ℂ (((x ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : SpatialHilbert H K)) w) : v = w := by
  apply ext_inner_left ℂ
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul x η => exact h x η
    | add a b ha hb =>
      simpa only [UniformSpace.Completion.coe_add, inner_add_left] using congrArg₂ (· + ·) ha hb

omit [CompleteSpace H] in
private theorem operator_eq_of_diagonal {S T : H →L[ℂ] H}
    (h : ∀ x, inner ℂ x (S x) = inner ℂ x (T x)) : S = T := by
  have he : S.toLinearMap = T.toLinearMap := (ext_inner_map _ _).mp (fun x => by
    exact (inner_conj_symm (S x) x).symm.trans
      ((congrArg (starRingEnd ℂ) (h x)).trans (inner_conj_symm (T x) x)))
  ext x
  exact congrArg (fun L : H →ₗ[ℂ] H => L x) he

/-- Scalar right-leg slices force an operator to lie entirely in the first leg. -/
theorem spatial_eq_left_of_scalar_right_slices
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (Ω : K) (hΩ : ‖Ω‖ = 1)
    (hscalar : ∀ x : H, ∃ z : ℂ, rightTensorSlice x T = z • (1 : K →L[ℂ] K)) :
    T = spatialLeft (K := K) (tensorVectorSlice Ω T) := by
  let A : H →L[ℂ] H := tensorVectorSlice Ω T
  have hcross (η ζ : K) :
      (tensorVector η).adjoint ∘L T ∘L tensorVector ζ = inner ℂ η ζ • A := by
    apply operator_eq_of_diagonal
    intro x
    obtain ⟨z, hz⟩ := hscalar x
    have hηζ : inner ℂ (tensorVector η x) (T (tensorVector ζ x)) =
        inner ℂ η (rightTensorSlice x T ζ) := by
      rw [rightTensorSlice_apply, ContinuousLinearMap.adjoint_inner_right]
      rfl
    have hA : inner ℂ x (A x) = z := by
      change inner ℂ x ((tensorVector Ω).adjoint (T (tensorVector Ω x))) = z
      rw [ContinuousLinearMap.adjoint_inner_right]
      rw [show inner ℂ (tensorVector Ω x) (T (tensorVector Ω x)) =
        inner ℂ Ω (rightTensorSlice x T Ω) by
          rw [rightTensorSlice_apply, ContinuousLinearMap.adjoint_inner_right]; rfl]
      rw [hz]
      simp only [smul_apply, one_apply_eq_self, inner_smul_right,
        inner_self_eq_norm_sq_to_K, hΩ, one_pow, RCLike.ofReal_one, mul_one]
    change inner ℂ x ((tensorVector η).adjoint (T (tensorVector ζ x))) =
      inner ℂ x ((inner ℂ η ζ) • (A x))
    rw [ContinuousLinearMap.adjoint_inner_right, hηζ, hz, inner_smul_right, hA]
    simp only [smul_apply, one_apply_eq_self, inner_smul_right]
    ring
  apply spatialTensorOp_ext
  intro x ζ
  apply spatialTensor_vector_ext
  intro y η
  have he := congrArg (fun B : H →L[ℂ] H => inner ℂ y (B x)) (hcross η ζ)
  change inner ℂ y ((tensorVector η).adjoint (T (tensorVector ζ x))) = _ at he
  rw [ContinuousLinearMap.adjoint_inner_right] at he
  change inner ℂ (tensorVector η y) (T (tensorVector ζ x)) = _
  rw [he]
  change inner ℂ y ((inner ℂ η ζ) • (A x)) =
    inner ℂ (tensorVector η y) (spatialTensorOp A 1 (tensorVector ζ x))
  simp only [tensorVector_apply, spatialTensorOp_coe, TensorProduct.mapL_tmul,
    one_apply_eq_self, UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul,
    inner_smul_right]
  ring

/-- The first-leg relative-commutant identity for the product-state
centralizer follows from local swaps and concrete vector slices. -/
theorem spatial_relative_commutant_of_local_swaps
    (M : VonNeumannAlgebra H) {D : VonNeumannAlgebra K} {Ω : K}
    (L : LocalProductSwaps D Ω) (hΩ : ‖Ω‖ = 1)
    (hsep : Function.Injective (algebraVectorMap D Ω))
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (hT : T ∈ spatialProductAlgebra M D)
    (hcomm : ∀ u : unitary (K →L[ℂ] K), (u : K →L[ℂ] K) ∈ D →
      ProductStateCentralizes D Ω u → spatialRight (u : K →L[ℂ] K) * T =
        T * spatialRight (u : K →L[ℂ] K)) :
    ∃ a ∈ M, T = spatialLeft (K := K) a := by
  refine ⟨tensorVectorSlice Ω T, tensorVectorSlice_mem M D Ω T hT, ?_⟩
  exact spatial_eq_left_of_scalar_right_slices T Ω hΩ
    (rightTensorSlice_scalar_of_local_swaps M L hΩ hsep T hT hcomm)


/-- Tensoring a factor with the product algebra remains factorial. This
uses the proved relative-commutant identity rather than a tensor-factor
classification assumption. -/
theorem scalarCenter_spatialProduct_of_local_swaps
    (M : VonNeumannAlgebra H) (hM : ScalarCenter M)
    {D : VonNeumannAlgebra K} {Ω : K}
    (L : LocalProductSwaps D Ω) (hΩ : ‖Ω‖ = 1)
    (hsep : Function.Injective (algebraVectorMap D Ω)) :
    ScalarCenter (spatialProductAlgebra M D) := by
  intro T hT hcentral
  obtain ⟨a, ha, rfl⟩ := spatial_relative_commutant_of_local_swaps M L hΩ hsep T hT
    (fun u hu _ => hcentral _ (spatialRight_mem_product M D hu))
  have hac : ∀ x ∈ M, x * a = a * x := by
    intro x hx
    have he := hcentral _ (spatialLeft_mem_product M D hx)
    change spatialLeft (K := K) x * spatialLeft (K := K) a =
      spatialLeft (K := K) a * spatialLeft (K := K) x at he
    rw [← map_mul, ← map_mul] at he
    have hs := congrArg (tensorVectorSlice Ω) he
    simpa only [tensorVectorSlice_spatialLeft Ω hΩ] using hs
  obtain ⟨z, hz⟩ := hM a ha hac
  refine ⟨z, ?_⟩
  rw [hz, map_smul, map_one]

end

end KadisonKastler

end OAI
