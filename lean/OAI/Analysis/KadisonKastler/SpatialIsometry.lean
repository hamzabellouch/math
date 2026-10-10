import OAI.Analysis.KadisonKastler.SpatialAssociator

namespace OAI

/-! # Bounded maps and isometries between spatial Hilbert tensors

The rectangular tensor map respects composition and adjoints. In particular,
the tensor of a closed-subspace inclusion is an isometry whose range
projection is the spatial amplification of the original projection.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K E F G J : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]

theorem spatialLinearMap_ext {S T : SpatialHilbert H K →L[ℂ] E}
    (h : ∀ x : H, ∀ y : K,
      S ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) =
      T ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K)) : S = T := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq S.continuous T.continuous
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact h x y
    | add x y hx hy =>
      simpa only [UniformSpace.Completion.coe_add, map_add] using congrArg₂ (· + ·) hx hy

def spatialMap (a : H →L[ℂ] E) (b : K →L[ℂ] F) :
    SpatialHilbert H K →L[ℂ] SpatialHilbert E F :=
  (TensorProduct.mapL a b).completion

@[simp] theorem spatialMap_tmul (a : H →L[ℂ] E) (b : K →L[ℂ] F) (x : H) (y : K) :
    spatialMap a b ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) =
      ((a x ⊗ₜ[ℂ] b y : E ⊗[ℂ] F) : SpatialHilbert E F) := by
  simp only [spatialMap, ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]

theorem spatialMap_comp (a : E →L[ℂ] G) (b : F →L[ℂ] J)
    (c : H →L[ℂ] E) (d : K →L[ℂ] F) :
    (spatialMap a b).comp (spatialMap c d) = spatialMap (a.comp c) (b.comp d) := by
  apply spatialLinearMap_ext
  intro x y
  simp

@[simp] theorem spatialMap_id :
    spatialMap (ContinuousLinearMap.id ℂ H) (ContinuousLinearMap.id ℂ K) =
      ContinuousLinearMap.id ℂ (SpatialHilbert H K) := by
  apply spatialLinearMap_ext
  intro x y
  simp

def spatialIsometry (a : H →ₗᵢ[ℂ] E) (b : K →ₗᵢ[ℂ] F) :
    SpatialHilbert H K →ₗᵢ[ℂ] SpatialHilbert E F :=
  (TensorProduct.mapIsometry a b).completion

theorem spatialIsometry_toContinuousLinearMap (a : H →ₗᵢ[ℂ] E) (b : K →ₗᵢ[ℂ] F) :
    (spatialIsometry a b).toContinuousLinearMap =
      spatialMap a.toContinuousLinearMap b.toContinuousLinearMap := by
  simp only [spatialIsometry, LinearIsometry.toContinuousLinearMap_completion,
    TensorProduct.toContinuousLinearMap_mapIsometry, spatialMap]

@[simp] theorem spatialIsometry_tmul (a : H →ₗᵢ[ℂ] E) (b : K →ₗᵢ[ℂ] F)
    (x : H) (y : K) :
    spatialIsometry a b ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) =
      ((a x ⊗ₜ[ℂ] b y : E ⊗[ℂ] F) : SpatialHilbert E F) := by
  change (spatialIsometry a b).toContinuousLinearMap _ = _
  rw [spatialIsometry_toContinuousLinearMap]
  exact spatialMap_tmul _ _ _ _

variable [CompleteSpace H] [CompleteSpace K] [CompleteSpace E] [CompleteSpace F]

theorem spatialMap_adjoint (a : H →L[ℂ] E) (b : K →L[ℂ] F) :
    (spatialMap a b).adjoint = spatialMap a.adjoint b.adjoint := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ =>
      simpa only [UniformSpace.Completion.coe_add, map_add, inner_add_left] using
        congrArg₂ (· + ·) h₁ h₂
    | tmul x₁ x₂ =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ =>
        simpa only [UniformSpace.Completion.coe_add, map_add, inner_add_right] using
          congrArg₂ (· + ·) h₁ h₂
      | tmul y₁ y₂ =>
        simp only [spatialMap_tmul, UniformSpace.Completion.inner_coe,
          TensorProduct.inner_tmul, ContinuousLinearMap.adjoint_inner_left]

def spatialSubspaceInclusion (V : Submodule ℂ H) :
    SpatialHilbert V K →ₗᵢ[ℂ] SpatialHilbert H K :=
  spatialIsometry V.subtypeₗᵢ (.id : K →ₗᵢ[ℂ] K)

theorem spatialSubspaceInclusion_projection (V : Submodule ℂ H) [CompleteSpace V] :
    (spatialSubspaceInclusion (K := K) V).toContinuousLinearMap.comp
      (spatialSubspaceInclusion (K := K) V).toContinuousLinearMap.adjoint =
        spatialLeft (K := K) V.starProjection := by
  rw [show (spatialSubspaceInclusion (K := K) V).toContinuousLinearMap =
      spatialMap V.subtypeL (ContinuousLinearMap.id ℂ K) from
    spatialIsometry_toContinuousLinearMap _ _]
  rw [spatialMap_adjoint, spatialMap_comp, Submodule.adjoint_subtypeL]
  apply spatialLinearMap_ext
  intro x y
  simp only [spatialMap_tmul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.adjoint_id]
  change _ = spatialTensorOp V.starProjection 1 _
  simp only [spatialTensorOp_coe, TensorProduct.mapL_tmul, one_apply_eq_self]
  rfl

end

end KadisonKastler

end OAI
