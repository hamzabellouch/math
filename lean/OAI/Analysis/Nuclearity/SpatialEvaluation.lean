import OAI.Analysis.Nuclearity.MinimalTensorAlgebraic

namespace OAI

/-! Faithful spatial representations of the minimal completion. -/

noncomputable section
open scoped TensorProduct ENNReal
open UniformSpace

namespace WeakPureInfiniteness

universe u v
variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

/-- Evaluation at one of the spatial representations defining the norm. -/
def minimalSpatialEvaluation (π : SpatialRepresentation A B) :
    MinimalTensor A B →⋆ₙₐ[ℂ] (π.space →L[ℂ] π.space) where
  toFun z := z.val π
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp] theorem minimalSpatialEvaluation_elementary (π : SpatialRepresentation A B)
    (a : A) (b : B) :
    minimalSpatialEvaluation π (minimalElementary a b) =
      (TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion := rfl

theorem norm_spatialSum_le_faithful (π : SpatialRepresentation A B)
    (hπ : Function.Injective π.leftRep) (hρ : Function.Injective π.rightRep)
    {I : Type*} (s : Finset I) (a : I → A) (b : I → B) :
    ‖∑ i ∈ s, spatialElementary (a i) (b i)‖ ≤
      ‖∑ i ∈ s, TensorProduct.mapL (π.leftRep (a i)) (π.rightRep (b i))‖ := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  apply lp.norm_le_of_forall_le
    (C := ‖∑ i ∈ s, TensorProduct.mapL (π.leftRep (a i)) (π.rightRep (b i))‖)
    (ContinuousLinearMap.opNorm_nonneg _)
  intro σ
  rw [spatialSum_apply, norm_completion]
  calc
    _ ≤ ‖∑ i ∈ s, TensorProduct.mapL (σ.leftRep (a i)) (π.rightRep (b i))‖ :=
      tensor_norm_le_faithful_finset s (fun i => σ.leftRep (a i)) b π.rightRep σ.rightRep hρ
    _ = ‖∑ i ∈ s, TensorProduct.mapL (π.rightRep (b i)) (σ.leftRep (a i))‖ :=
      norm_tensorSum_flip s _ _
    _ ≤ ‖∑ i ∈ s, TensorProduct.mapL (π.rightRep (b i)) (π.leftRep (a i))‖ :=
      tensor_norm_le_faithful_finset s (fun i => π.rightRep (b i)) a π.leftRep σ.leftRep hπ
    _ = _ := norm_tensorSum_flip s _ _

theorem minimalSpatialEvaluation_norm_sum (π : SpatialRepresentation A B)
    (hπ : Function.Injective π.leftRep) (hρ : Function.Injective π.rightRep)
    {I : Type*} [Fintype I] (a : I → A) (b : I → B) :
    ‖minimalSpatialEvaluation π (∑ i, minimalElementary (a i) (b i))‖ =
      ‖∑ i, minimalElementary (a i) (b i)‖ := by
  have he : minimalSpatialEvaluation π (∑ i, minimalElementary (a i) (b i)) =
      (∑ i, TensorProduct.mapL (π.leftRep (a i)) (π.rightRep (b i))).completion := by
    change ((minimalTensorSubalgebra A B).subtype (∑ i, minimalElementary (a i) (b i))) π = _
    simp only [map_sum]
    exact spatialSum_apply Finset.univ a b π
  rw [he, norm_completion]
  change _ = ‖(minimalTensorSubalgebra A B).subtype (∑ i, minimalElementary (a i) (b i))‖
  simp only [map_sum]
  change ‖∑ i, TensorProduct.mapL (π.leftRep (a i)) (π.rightRep (b i))‖ =
    ‖∑ i, spatialElementary (a i) (b i)‖
  exact le_antisymm (norm_tensorSum_le_spatial_any Finset.univ a b π.leftRep π.rightRep)
    (norm_spatialSum_le_faithful π hπ hρ Finset.univ a b)

theorem minimalSpatialEvaluation_isometry (π : SpatialRepresentation A B)
    (hπ : Function.Injective π.leftRep) (hρ : Function.Injective π.rightRep) :
    Isometry (minimalSpatialEvaluation π) := by
  let E := minimalSpatialEvaluation π
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  refine (UnitalMinimalTensor.algebraicMap_dense (A := A) (B := B)).induction_on
    (p := fun x => ‖E x‖ = ‖x‖) x ?_ ?_
  · exact isClosed_eq (nonUnitalStarHom_continuous E).norm continuous_norm
  · intro z
    obtain ⟨n, a, b, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
    simp only [map_sum, UnitalMinimalTensor.algebraicMap_tmul]
    simpa only [map_sum] using minimalSpatialEvaluation_norm_sum π hπ hρ a b

end WeakPureInfiniteness

end

end OAI
