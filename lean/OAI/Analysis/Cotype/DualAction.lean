import OAI.Analysis.Cotype.EquivariantLifts

namespace OAI

noncomputable section
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def dualIsometry (e : X ≃ₗᵢ[ℝ] X) : (X →L[ℝ] ℝ) ≃ₗᵢ[ℝ] (X →L[ℝ] ℝ) where
  toFun f := f.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  invFun f := f.comp e.toContinuousLinearEquiv.toContinuousLinearMap
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp
  norm_map' f := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
      intro x
      simpa using f.le_opNorm (e.symm x)
    · apply f.opNorm_le_bound (norm_nonneg _)
      intro x
      have h := (f.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap).le_opNorm (e x)
      simpa using h

@[simp] theorem dualIsometry_apply (e : X ≃ₗᵢ[ℝ] X) (f : X →L[ℝ] ℝ) (x : X) :
    dualIsometry e f x = f (e.symm x) := rfl

variable {Γ : Type*} [Group Γ]

def dualAction (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) : Γ →* ((X →L[ℝ] ℝ) ≃ₗᵢ[ℝ] (X →L[ℝ] ℝ)) where
  toFun g := dualIsometry (ρ g)
  map_one' := by
    ext f x
    change f ((ρ 1).symm x) = f x
    rw [map_one]
    rfl
  map_mul' g h := by
    ext f x
    simp [dualIsometry_apply, map_mul, LinearIsometryEquiv.mul_def]

theorem dualAction_pairing (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) (g : Γ) (f : X →L[ℝ] ℝ) (x : X) :
    dualAction ρ g f (ρ g x) = f x := by
  change f ((ρ g).symm (ρ g x)) = _
  simp

end Cotype

end

end OAI
