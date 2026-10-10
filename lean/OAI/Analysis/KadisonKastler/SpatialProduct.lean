import OAI.Analysis.TracialSplitting.SpatialTensor
import OAI.Analysis.KadisonKastler.GeneratedAlgebraGap

namespace OAI

/-! # The concrete spatial tensor product used in the fixed-factor reduction

The spatial von Neumann algebra is the bicommutant of the bounded tensor
operators. Vector slices act on the completed tensor Hilbert space.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev spatialLeft : (H →L[ℂ] H) →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  Pureness.spatialLeftHom (K := K) (StarAlgHom.id ℂ (H →L[ℂ] H))

abbrev spatialRight : (K →L[ℂ] K) →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  Pureness.spatialRightHom (H := H) (StarAlgHom.id ℂ (K →L[ℂ] K))

/-- The spatial von Neumann tensor product in the given representations. -/
def spatialProductAlgebra (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K) :
    VonNeumannAlgebra (SpatialHilbert H K) :=
  generatedVonNeumannAlgebra
    ((M.toStarSubalgebra.map spatialLeft) ⊔ (D.toStarSubalgebra.map spatialRight))

theorem spatialLeft_mem_product (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    {x : H →L[ℂ] H} (hx : x ∈ M) :
    spatialLeft (K := K) x ∈ spatialProductAlgebra M D := by
  let A : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    M.toStarSubalgebra.map (spatialLeft (H := H) (K := K))
  let B : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    D.toStarSubalgebra.map (spatialRight (H := H) (K := K))
  apply subset_generatedVonNeumannAlgebra (A ⊔ B)
  have hx' : spatialLeft (K := K) x ∈ A := ⟨x, hx, rfl⟩
  exact (show A ≤ A ⊔ B from le_sup_left) hx'

theorem spatialRight_mem_product (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    {x : K →L[ℂ] K} (hx : x ∈ D) :
    spatialRight (H := H) x ∈ spatialProductAlgebra M D := by
  let A : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    M.toStarSubalgebra.map (spatialLeft (H := H) (K := K))
  let B : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    D.toStarSubalgebra.map (spatialRight (H := H) (K := K))
  apply subset_generatedVonNeumannAlgebra (A ⊔ B)
  have hx' : spatialRight (H := H) x ∈ B := ⟨x, hx, rfl⟩
  exact (show B ≤ A ⊔ B from le_sup_right) hx'

/-- The map inserting a fixed vector in the second tensor leg. -/
def tensorVector (ξ : K) : H →L[ℂ] SpatialHilbert H K :=
  UniformSpace.Completion.toComplL.comp ((TensorProduct.mkL ℂ H K).flip ξ)

omit [CompleteSpace H] [CompleteSpace K] in
@[simp]
theorem tensorVector_apply (ξ : K) (x : H) :
    tensorVector ξ x = ((x ⊗ₜ[ℂ] ξ : H ⊗[ℂ] K) : SpatialHilbert H K) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
@[simp]
theorem norm_tensorVector_apply (ξ : K) (x : H) :
    ‖tensorVector ξ x‖ = ‖x‖ * ‖ξ‖ := by
  simp only [tensorVector_apply, UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul]

omit [CompleteSpace H] [CompleteSpace K] in
theorem norm_tensorVector_le (ξ : K) : ‖tensorVector (H := H) ξ‖ ≤ ‖ξ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [norm_tensorVector_apply, mul_comm]

/-- The vector slice is concrete compression by the tensor-vector map. -/
def tensorVectorSlice (ξ : K) :
    (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun T := (tensorVector ξ).adjoint ∘L T ∘L tensorVector ξ
  map_add' S T := by ext x; simp
  map_smul' c T := by ext x; simp

omit [CompleteSpace K] in
@[simp]
theorem tensorVectorSlice_apply (ξ : K)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (x : H) :
    tensorVectorSlice ξ T x = (tensorVector ξ).adjoint (T (tensorVector ξ x)) := rfl

omit [CompleteSpace K] in
/-- Slicing a simple tensor gives its actual vector-state coefficient. -/
theorem tensorVectorSlice_tensor (ξ : K) (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    tensorVectorSlice ξ (spatialTensorOp S T) = (inner ℂ ξ (T ξ)) • S := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [tensorVectorSlice_apply, ContinuousLinearMap.adjoint_inner_right]
  simp only [tensorVector_apply, spatialTensorOp_coe, TensorProduct.mapL_tmul,
    UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul, smul_apply,
    inner_smul_right]
  ring

/-- A unit vector makes the slice a left inverse of the first-leg inclusion. -/
theorem tensorVectorSlice_spatialLeft (ξ : K) (hξ : ‖ξ‖ = 1) (S : H →L[ℂ] H) :
    tensorVectorSlice ξ (spatialLeft S) = S := by
  change tensorVectorSlice ξ (spatialTensorOp S 1) = S
  rw [tensorVectorSlice_tensor, one_apply_eq_self, inner_self_eq_norm_sq_to_K, hξ]
  simp

omit [CompleteSpace K] in
theorem norm_tensorVectorSlice_le (ξ : K) (hξ : ‖ξ‖ = 1)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :
    ‖tensorVectorSlice ξ T‖ ≤ ‖T‖ := by
  change ‖(tensorVector ξ).adjoint ∘L T ∘L tensorVector ξ‖ ≤ ‖T‖
  have hV : ‖tensorVector (H := H) ξ‖ ≤ 1 := (norm_tensorVector_le ξ).trans_eq hξ
  have hVs : ‖(tensorVector (H := H) ξ).adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hV
  calc
    _ ≤ (‖(tensorVector ξ).adjoint‖ * ‖T‖) * ‖tensorVector ξ‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖T‖) * 1 := by gcongr
    _ = ‖T‖ := by ring

end

end KadisonKastler

end OAI
