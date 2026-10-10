import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeCompressionGeometry
import OAI.Analysis.KadisonSimilarity.FreeProduct.PropagationTheorem

namespace OAI

/-!
# Vacuum coefficients of a head tensor action

The exceptional-projection formula in propagation follows from the actual
head action on the completed tensor product. It does not need to be assumed
separately for every vector or every term of the Haar sequence.
-/

noncomputable section
namespace KadisonSimilarity

open ContinuousLinearMap
open scoped TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The adjoint of endpoint insertion is the completed tensor slice. -/
theorem hilbertTensorInsert_adjoint (Ω : E) :
    (hilbertTensorInsert (H := F) Ω).adjoint = tensorSlice Ω := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro a x
  apply ext_inner_left ℂ
  intro y
  rw [adjoint_inner_right, inner_hilbertTensorInsert, tensorSlice_insert, inner_smul_right]

/-- The actual vacuum subspace in a completed head-tail tensor product. -/
def vacuumSubspace (Ω : E) : Submodule ℂ (HilbertTensor E F) :=
  (hilbertTensorInsert Ω).range

/-- Subtracting the vacuum coefficient leaves an orthogonal vector. -/
theorem vacuum_remainder_orthogonal (Ω : E) (hΩ : ‖Ω‖ = 1) (z : HilbertTensor E F) :
    z - hilbertTensorInsert Ω (tensorSlice Ω z) ∈ (vacuumSubspace (F := F) Ω)ᗮ := by
  have hzero (x : F) : inner ℂ (hilbertTensorInsert Ω x)
      (z - hilbertTensorInsert Ω (tensorSlice Ω z)) = 0 := by
    have hfirst : inner ℂ (hilbertTensorInsert Ω x) z = inner ℂ x (tensorSlice Ω z) := by
      exact (adjoint_inner_right (hilbertTensorInsert Ω) x z).symm.trans
        (congrArg (fun T : HilbertTensor E F →L[ℂ] F => inner ℂ x (T z))
          (hilbertTensorInsert_adjoint Ω))
    have hsecond : inner ℂ (hilbertTensorInsert Ω x)
        (hilbertTensorInsert Ω (tensorSlice Ω z)) = inner ℂ x (tensorSlice Ω z) := by
      exact (inner_hilbertTensorInsert Ω Ω x (tensorSlice Ω z)).trans (by
        rw [inner_self_eq_norm_sq_to_K, hΩ]
        simp)
    exact (inner_sub_right _ _ _).trans (sub_eq_zero.mpr (hfirst.trans hsecond.symm))
  rintro w ⟨x, rfl⟩
  exact hzero x

/-- The vacuum projection exists directly from the tensor decomposition. -/
theorem vacuumSubspace_hasOrthogonalProjection (Ω : E) (hΩ : ‖Ω‖ = 1) :
    (vacuumSubspace (F := F) Ω).HasOrthogonalProjection where
  exists_orthogonal z := ⟨hilbertTensorInsert Ω (tensorSlice Ω z),
    ⟨tensorSlice Ω z, rfl⟩, vacuum_remainder_orthogonal Ω hΩ z⟩

/-- The orthogonal projection onto the vacuum subspace is insertion followed
by its adjoint. -/
theorem vacuumSubspace_starProjection (Ω : E) (hΩ : ‖Ω‖ = 1)
    [(vacuumSubspace (F := F) Ω).HasOrthogonalProjection] :
    (vacuumSubspace (F := F) Ω).starProjection =
      firstLetterProjection Ω (ContinuousLinearMap.id ℂ F) := by
  ext z
  change (vacuumSubspace (F := F) Ω).starProjection z =
    hilbertTensorInsert Ω ((hilbertTensorInsert Ω).adjoint z)
  rw [hilbertTensorInsert_adjoint]
  exact (vacuumSubspace (F := F) Ω).eq_starProjection_of_mem_orthogonal
    ⟨tensorSlice Ω z, rfl⟩ (vacuum_remainder_orthogonal Ω hΩ z)

/-- Act on the head factor while leaving the completed tail unchanged. -/
def tensorHeadAction (X : E →L[ℂ] E) : HilbertTensor E F →L[ℂ] HilbertTensor E F :=
  (TensorProduct.mapL X (ContinuousLinearMap.id ℂ F)).completion

omit [CompleteSpace F] in
@[simp] theorem tensorHeadAction_insert (X : E →L[ℂ] E) (a : E) (x : F) :
    tensorHeadAction X (hilbertTensorInsert a x) = hilbertTensorInsert (X a) x := by
  change (TensorProduct.mapL X (ContinuousLinearMap.id ℂ F)).completion
    ((a ⊗ₜ[ℂ] x : TensorProduct ℂ E F) : UniformSpace.Completion (TensorProduct ℂ E F)) =
      ((X a ⊗ₜ[ℂ] x : TensorProduct ℂ E F) : UniformSpace.Completion (TensorProduct ℂ E F))
  simp only [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul,
    ContinuousLinearMap.id_apply]

variable [CompleteSpace E]

/-- Moving the head operator to the slicing vector takes its adjoint. -/
theorem tensorSlice_head (Ω : E) (X : E →L[ℂ] E) :
    (tensorSlice (F := F) Ω).comp (tensorHeadAction X) = tensorSlice (X.adjoint Ω) := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro a x
  simp only [comp_apply, tensorHeadAction_insert, tensorSlice_insert]
  rw [adjoint_inner_left]

/-- The full vacuum projection after multiplication is the slice against
`X*Ω`, followed by insertion of `Ω`. -/
theorem firstLetterProjection_head (Ω : E) (X : E →L[ℂ] E) :
    (firstLetterProjection Ω (ContinuousLinearMap.id ℂ F)).comp (tensorHeadAction X) =
      (hilbertTensorInsert Ω).comp (tensorSlice (X.adjoint Ω)) := by
  simp only [firstLetterProjection, ContinuousLinearMap.id_comp,
    hilbertTensorInsert_adjoint, ContinuousLinearMap.comp_assoc, tensorSlice_head]

/-- In particular the actual head action of an orthonormal adjoint-vector
sequence has vanishing vacuum coefficient on every fixed tensor. -/
theorem firstLetterProjection_head_tendsto_zero (Ω : E) (X : ℕ → E →L[ℂ] E)
    (hX : Orthonormal ℂ (fun n => (X n).adjoint Ω)) (z : HilbertTensor E F) :
    Filter.Tendsto (fun n => firstLetterProjection Ω (ContinuousLinearMap.id ℂ F)
      (tensorHeadAction (X n) z)) Filter.atTop (nhds 0) := by
  have ht := tensorSlice_tendsto_zero_of_orthonormal _ hX z
  have hc := ((hilbertTensorInsert (H := F) Ω).continuous.tendsto 0).comp ht
  have hformula (n : ℕ) : firstLetterProjection Ω (ContinuousLinearMap.id ℂ F)
      (tensorHeadAction (X n) z) = hilbertTensorInsert Ω (tensorSlice ((X n).adjoint Ω) z) :=
    congrArg (fun T : HilbertTensor E F →L[ℂ] HilbertTensor E F => T z)
      (firstLetterProjection_head Ω (X n))
  simpa only [Function.comp_def, ← hformula, map_zero] using hc

section Coordinates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Transport the actual vacuum subspace through tracial word coordinates. -/
abbrev tracialVacuumSubspace (U : H ≃ₗᵢ[ℂ] HilbertTensor E F) (Ω : E) : Submodule ℂ H :=
  (vacuumSubspace (F := F) Ω).map U.symm.toLinearIsometry.toLinearMap

omit [CompleteSpace E] in
/-- The transported vacuum subspace also has its orthogonal projection. -/
theorem tracialVacuumSubspace_hasOrthogonalProjection
    (U : H ≃ₗᵢ[ℂ] HilbertTensor E F) (Ω : E) (hΩ : ‖Ω‖ = 1) :
    (tracialVacuumSubspace U Ω).HasOrthogonalProjection := by
  let := vacuumSubspace_hasOrthogonalProjection (F := F) Ω hΩ
  exact Submodule.HasOrthogonalProjection.map_linearIsometryEquiv'
    (vacuumSubspace (F := F) Ω) U.symm

omit [CompleteSpace E] in
/-- The projection-coordinate identity follows from its actual subspace
construction, rather than being additional word-model data. -/
theorem tracialVacuumSubspace_projection_coordinates
    (U : H ≃ₗᵢ[ℂ] HilbertTensor E F) (Ω : E) (hΩ : ‖Ω‖ = 1)
    [(vacuumSubspace (F := F) Ω).HasOrthogonalProjection]
    [(tracialVacuumSubspace U Ω).HasOrthogonalProjection] (z : H) :
    U ((tracialVacuumSubspace U Ω).starProjection z) =
      firstLetterProjection Ω (ContinuousLinearMap.id ℂ F) (U z) := by
  have h := U.symm.toLinearIsometry.map_starProjection (vacuumSubspace (F := F) Ω) (U z)
  have hu := congrArg U h
  simpa only [tracialVacuumSubspace, LinearIsometryEquiv.coe_toLinearIsometry,
    U.apply_symm_apply, U.symm_apply_apply, vacuumSubspace_starProjection Ω hΩ] using hu.symm

/-- Transport the head-action formula to a tracial word realization. The two
hypotheses are the ordinary coordinate identities for multiplication and for
the vacuum projection. -/
theorem vacuum_slice_in_coordinates
    (U : H ≃ₗᵢ[ℂ] HilbertTensor E F) (Ω : E)
    (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (X : H →L[ℂ] H) (T : E →L[ℂ] E)
    (hP : ∀ z, U (P.starProjection z) =
      firstLetterProjection Ω (ContinuousLinearMap.id ℂ F) (U z))
    (hX : ∀ z, U (X z) = tensorHeadAction T (U z)) (z : H) :
    P.starProjection (X z) = U.symm
      (hilbertTensorInsert Ω (tensorSlice (T.adjoint Ω) (U z))) := by
  apply U.injective
  rw [hP, hX, U.apply_symm_apply]
  exact congrArg (fun A : HilbertTensor E F →L[ℂ] HilbertTensor E F => A (U z))
    (firstLetterProjection_head Ω T)

/-- Thus the vanishing projection required for propagation follows directly
from the head-action representation and orthonormality of the adjoint letters. -/
theorem vacuum_projection_tendsto_zero_of_head_coordinates
    (U : H ≃ₗᵢ[ℂ] HilbertTensor E F) (Ω : E)
    (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (X : ℕ → H →L[ℂ] H) (T : ℕ → E →L[ℂ] E)
    (hP : ∀ z, U (P.starProjection z) =
      firstLetterProjection Ω (ContinuousLinearMap.id ℂ F) (U z))
    (hX : ∀ n z, U (X n z) = tensorHeadAction (T n) (U z))
    (horth : Orthonormal ℂ (fun n => (T n).adjoint Ω)) (z : H) :
    Filter.Tendsto (fun n => P.starProjection (X n z)) Filter.atTop (nhds 0) := by
  have ht := firstLetterProjection_head_tendsto_zero Ω T horth (U z)
  have hc := (U.symm.continuous.tendsto 0).comp ht
  have hformula (n : ℕ) : U.symm
      (firstLetterProjection Ω (ContinuousLinearMap.id ℂ F) (tensorHeadAction (T n) (U z))) =
      P.starProjection (X n z) := by
    apply U.injective
    rw [U.apply_symm_apply, hP, hX]
  simpa only [Function.comp_def, hformula, map_zero] using hc

end Coordinates
end KadisonSimilarity

end

end OAI
