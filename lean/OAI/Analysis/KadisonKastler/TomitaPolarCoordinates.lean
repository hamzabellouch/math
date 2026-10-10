import OAI.Analysis.KadisonKastler.TomitaResolventEndpoints
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

namespace OAI

/-! # Polar coordinates for the closed Tomita graph

The first-coordinate map has dense range and zero kernel. Extending the
isometry between the ranges of its adjoint and the positive graph root
identifies the graph Hilbert space with the original Hilbert space.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

private theorem denseRange_of_adjoint_injective
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] K) (hA : Function.Injective A.adjoint) : DenseRange A := by
  change Dense (A.range : Set K)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, A.orthogonal_range]
  exact LinearMap.ker_eq_bot.mpr hA

/-- First coordinate on the graph Hilbert space. -/
def tomitaGraphFirst (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    rescaledGraphSubspace M J Ω 1 →L[ℂ] H :=
  (Generator.tupleSingle (H := H) (0 : Fin 2)).adjoint.comp
    (rescaledGraphSubspace M J Ω 1).subtypeL

@[simp] theorem tomitaGraphFirst_apply (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (ξ : rescaledGraphSubspace M J Ω 1) : tomitaGraphFirst (M := M) J Ω ξ = ξ.val 0 := by
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x ((Generator.tupleSingle (H := H) (0 : Fin 2)).adjoint ξ.val) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [PiLp.inner_apply, Fin.sum_univ_two, Generator.tupleSingle_apply, Pi.single_apply]

@[simp] theorem tomitaGraphFirst_adjoint_apply (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (x : H) :
    ((tomitaGraphFirst (M := M) J Ω).adjoint x).val =
      rescaledGraphProjection M J Ω 1 (Generator.tupleSingle 0 x) := by
  simp only [tomitaGraphFirst, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, ContinuousLinearMap.adjoint_adjoint]
  rfl

theorem tomitaGraphFirst_mul_adjoint (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    (tomitaGraphFirst (M := M) J Ω).comp (tomitaGraphFirst (M := M) J Ω).adjoint =
      graphResolvent M J Ω 1 := by
  ext x
  rw [ContinuousLinearMap.comp_apply, tomitaGraphFirst_apply,
    tomitaGraphFirst_adjoint_apply]
  rfl

theorem tomitaGraphFirst_injective (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω)) :
    Function.Injective (tomitaGraphFirst (M := M) J Ω) := by
  intro ξ η h
  exact rescaledGraph_first_injective J Ω 1 hsep (by simpa only [tomitaGraphFirst_apply] using h)

/-- The positive square root of the bounded graph resolvent. -/
def tomitaGraphRoot (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) : H →L[ℂ] H :=
  CFC.sqrt (graphResolvent M J Ω 1)

theorem tomitaGraphRoot_selfAdjoint (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    IsSelfAdjoint (tomitaGraphRoot (M := M) J Ω) :=
  (CFC.sqrt_nonneg _).isSelfAdjoint

theorem tomitaGraphRoot_square (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    tomitaGraphRoot (M := M) J Ω * tomitaGraphRoot (M := M) J Ω = graphResolvent M J Ω 1 :=
  CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (graphResolvent_positive J Ω 1))

theorem tomitaGraphRoot_injective (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    Function.Injective (tomitaGraphRoot (M := M) J Ω) := by
  intro x y he
  apply sub_eq_zero.mp
  apply (graphResolvent_eq_zero_iff J Ω 1 hsep hcyc (x - y)).mp
  rw [← tomitaGraphRoot_square]
  change tomitaGraphRoot (M := M) J Ω (tomitaGraphRoot (M := M) J Ω (x - y)) = 0
  rw [map_sub, he, sub_self, map_zero]

theorem tomitaGraphRoot_dense (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    DenseRange (tomitaGraphRoot (M := M) J Ω) := by
  apply denseRange_of_adjoint_injective
  have he : (tomitaGraphRoot (M := M) J Ω).adjoint = tomitaGraphRoot (M := M) J Ω :=
    (tomitaGraphRoot_selfAdjoint J Ω).star_eq
  rw [he]
  exact tomitaGraphRoot_injective J Ω hsep hcyc

theorem tomitaGraphFirst_adjoint_norm (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (x : H) :
    ‖(tomitaGraphFirst (M := M) J Ω).adjoint x‖ = ‖tomitaGraphRoot (M := M) J Ω x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    ContinuousLinearMap.adjoint_adjoint, tomitaGraphFirst_mul_adjoint]
  have hs : (tomitaGraphRoot (M := M) J Ω).adjoint.comp (tomitaGraphRoot (M := M) J Ω) =
      graphResolvent M J Ω 1 := by
    change star (tomitaGraphRoot (M := M) J Ω) * tomitaGraphRoot (M := M) J Ω = _
    rw [(tomitaGraphRoot_selfAdjoint J Ω).star_eq, tomitaGraphRoot_square]
  rw [hs]

theorem tomitaGraphFirst_adjoint_dense (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω)) :
    DenseRange (tomitaGraphFirst (M := M) J Ω).adjoint := by
  apply denseRange_of_adjoint_injective
  rw [ContinuousLinearMap.adjoint_adjoint]
  exact tomitaGraphFirst_injective J Ω hsep

/-- Polar identification of H with the graph Hilbert space. -/
def tomitaPolarCoordinates (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    H ≃ₗᵢ[ℂ] rescaledGraphSubspace M J Ω 1 :=
  (LinearEquiv.refl ℂ H).extendOfIsometry (tomitaGraphRoot (M := M) J Ω).toLinearMap
    (tomitaGraphFirst (M := M) J Ω).adjoint.toLinearMap
    (tomitaGraphRoot_dense J Ω hsep hcyc) (tomitaGraphFirst_adjoint_dense J Ω hsep)
    (tomitaGraphFirst_adjoint_norm J Ω)

@[simp] theorem tomitaPolarCoordinates_root (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    tomitaPolarCoordinates J Ω hsep hcyc (tomitaGraphRoot (M := M) J Ω x) =
      (tomitaGraphFirst (M := M) J Ω).adjoint x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

end

end KadisonKastler

end OAI
