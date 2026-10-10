import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorLaws
import OAI.Analysis.WeakInfiniteness.TensorNorm

namespace OAI

/-! Elementary tensors in the original nonunital tensor ideal have their
first factor in the original algebra. This is the elementary lifting step
in transferring ideal generation from a unitization. -/

noncomputable section

namespace WeakPureInfiniteness

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def unitizationScalarHom : Unitization ℂ A →⋆ₙₐ[ℂ] ℂ where
  toFun a := a.fst
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

def unitizedTensorInclusion : MinimalTensor A B →⋆ₙₐ[ℂ] MinimalTensor (Unitization ℂ A) B :=
  minimalMapAny (Unitization.inrNonUnitalStarAlgHom ℂ A) (NonUnitalStarAlgHom.id ℂ B)

def unitizedTensorScalar : MinimalTensor (Unitization ℂ A) B →⋆ₙₐ[ℂ] MinimalTensor ℂ B :=
  minimalMapAny unitizationScalarHom (NonUnitalStarAlgHom.id ℂ B)

theorem unitizedTensorInclusion_isometry : Isometry (unitizedTensorInclusion (A := A) (B := B)) :=
  minimalMapAny_isometry _ _ Unitization.inr_injective Function.injective_id

@[simp] theorem unitizedTensorInclusion_elementary (a : A) (b : B) :
    unitizedTensorInclusion (minimalElementary a b) = minimalElementary (Unitization.inr a) b :=
  minimalMapAny_elementary _ _ a b

@[simp] theorem unitizedTensorScalar_elementary (a : Unitization ℂ A) (b : B) :
    unitizedTensorScalar (minimalElementary a b) = minimalElementary a.fst b :=
  minimalMapAny_elementary _ _ a b

@[simp] theorem unitizedTensorScalar_inclusion (x : MinimalTensor A B) :
    unitizedTensorScalar (unitizedTensorInclusion x) = 0 := by
  have he : (unitizedTensorScalar (A := A) (B := B)).comp unitizedTensorInclusion = 0 := by
    apply minimalTensor_hom_ext
    intro a b
    simp only [NonUnitalStarAlgHom.comp_apply, unitizedTensorInclusion_elementary,
      unitizedTensorScalar_elementary, Unitization.fst_inr, NonUnitalStarAlgHom.zero_apply]
    exact map_zero (minimalElementaryLeftLinear b)
  exact congrArg (fun f : MinimalTensor A B →⋆ₙₐ[ℂ] MinimalTensor ℂ B => f x) he

theorem unitizedTensor_elementary_lift (a : Unitization ℂ A) (b : B) (hb : b ≠ 0)
    (h : minimalElementary a b ∈ Set.range (unitizedTensorInclusion (A := A) (B := B))) :
    ∃ x : A, a = Unitization.inr x := by
  obtain ⟨z, hz⟩ := h
  have hzero : minimalElementary a.fst b = 0 := by
    rw [← unitizedTensorScalar_elementary, ← hz, unitizedTensorScalar_inclusion]
  have hn : ‖a.fst‖ * ‖b‖ = 0 := by rw [← norm_minimalElementary, hzero, norm_zero]
  have ha : a.fst = 0 := norm_eq_zero.mp
    ((mul_eq_zero.mp hn).resolve_right (norm_ne_zero_iff.mpr hb))
  refine ⟨a.snd, ?_⟩
  apply Unitization.ext
  · exact ha
  · rfl

end WeakPureInfiniteness

end

end OAI
