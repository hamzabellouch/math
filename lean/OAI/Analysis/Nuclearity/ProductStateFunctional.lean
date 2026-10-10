import OAI.Analysis.WeakInfiniteness.SpatialVectorStates
import OAI.Analysis.WeakInfiniteness.WordTensorDensity
import OAI.Analysis.WeakInfiniteness.States
import OAI.Analysis.WeakInfiniteness.UniformModels
import OAI.Analysis.TracialSplitting.PreparedBlocks

namespace OAI

/-! The bounded product functional, constructed in the spatial tensor
representation. No nuclearity or quotient assumption is used. -/

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder
open UniformSpace

namespace WeakPureInfiniteness

universe u v
variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem exists_product_state_functional (φ : A →ₚ[ℂ] ℂ) (ψ : B →ₚ[ℂ] ℂ)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1) :
    ∃ F : MinimalTensor A B →L[ℂ] ℂ, ‖F‖ ≤ 1 ∧
      ∀ a b, F (minimalElementary a b) = φ a * ψ b := by
  let H : ComplexHilbert.{max u v} := ⟨ULift.{v} φ.GNS⟩
  let K : ComplexHilbert.{max u v} := ⟨ULift.{u} ψ.GNS⟩
  let : NormedSpace ℂ H := inferInstance
  let : NormedSpace ℂ K := inferInstance
  let : CStarAlgebra (H →L[ℂ] H) := inferInstance
  let : CStarAlgebra (K →L[ℂ] K) := inferInstance
  let e : φ.GNS ≃ₗᵢ[ℂ] H := (LinearIsometryEquiv.ulift ℂ φ.GNS).symm
  let f : ψ.GNS ≃ₗᵢ[ℂ] K := (LinearIsometryEquiv.ulift ℂ ψ.GNS).symm
  let πA : A →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
    e.conjStarAlgEquiv.toNonUnitalStarAlgHom.comp φ.gnsNonUnitalStarAlgHom
  let πB : B →⋆ₙₐ[ℂ] (K →L[ℂ] K) :=
    f.conjStarAlgEquiv.toNonUnitalStarAlgHom.comp ψ.gnsNonUnitalStarAlgHom
  let π : SpatialRepresentation A B :=
    { left := H, right := K
      leftRep := πA, rightRep := πB }
  let ξ : H := e (Pureness.stateGNSVector φ)
  let η : K := f (Pureness.stateGNSVector ψ)
  let ζ : π.space := ((ξ ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : Completion (H ⊗[ℂ] K))
  have hζ : ‖ζ‖ = 1 := by
    simp only [ζ, Completion.norm_coe, TensorProduct.norm_tmul, ξ, η,
      LinearIsometryEquiv.norm_map, Pureness.stateGNSVector_norm φ hφ,
      Pureness.stateGNSVector_norm ψ hψ, one_mul]
  let S := (minimalTensorSubalgebra A B).toNonUnitalSubalgebra.toSubmodule.subtypeL
  let F := (spatialVectorFunctional π ζ).comp S
  refine ⟨F, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    calc
      ‖F z‖ ≤ ‖spatialVectorFunctional π ζ‖ * ‖S z‖ :=
        (spatialVectorFunctional π ζ).le_opNorm _
      _ ≤ (‖ζ‖ * ‖ζ‖) * ‖S z‖ := mul_le_mul_of_nonneg_right
        (norm_spatialVectorFunctional_le π ζ) (norm_nonneg _)
      _ = 1 * ‖z‖ := by simp only [hζ, one_mul]; rfl
  · intro a b
    change spatialVectorFunctional π ζ (spatialElementary a b) = _
    rw [spatialVectorFunctional_elementary]
    simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul]
    change inner ℂ (e (Pureness.stateGNSVector φ))
        (πA a (e (Pureness.stateGNSVector φ))) *
      inner ℂ (f (Pureness.stateGNSVector ψ))
        (πB b (f (Pureness.stateGNSVector ψ))) = _
    change inner ℂ (e (Pureness.stateGNSVector φ))
        (e (φ.gnsNonUnitalStarAlgHom a (e.symm (e (Pureness.stateGNSVector φ))))) *
      inner ℂ (f (Pureness.stateGNSVector ψ))
        (f (ψ.gnsNonUnitalStarAlgHom b (f.symm (f (Pureness.stateGNSVector ψ))))) = _
    rw [e.symm_apply_apply, f.symm_apply_apply]
    rw [e.inner_map_map, f.inner_map_map]
    exact congrArg₂ (· * ·) (Pureness.stateGNS_vector_value φ a)
      (Pureness.stateGNS_vector_value ψ b)

end WeakPureInfiniteness

end

end OAI
