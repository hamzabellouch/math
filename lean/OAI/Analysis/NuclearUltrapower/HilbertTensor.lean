import Mathlib

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower

section CompletionMaps
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Uniqueness on the dense original normed space. -/
theorem completion_map_ext {f g : UniformSpace.Completion E →L[ℂ] F}
    (h : ∀ x : E, f x = g x) : f = g := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq f.continuous g.continuous
  | ih x => exact h x

@[simp] theorem completed_add (f g : E →L[ℂ] F) :
    (f+g).completion = f.completion + g.completion := by
  apply completion_map_ext
  intro x
  simp [← UniformSpace.Completion.coe_add]

@[simp] theorem completed_smul (c : ℂ) (f : E →L[ℂ] F) :
    (c • f).completion = c • f.completion := by
  apply completion_map_ext
  intro x
  simp [← UniformSpace.Completion.coe_smul]

@[simp] theorem completed_zero : (0 : E →L[ℂ] F).completion = 0 := by
  apply completion_map_ext
  intro x
  simp

@[simp] theorem completed_comp (f : F →L[ℂ] G) (g : E →L[ℂ] F) :
    (f.comp g).completion = f.completion.comp g.completion := by
  apply completion_map_ext
  intro x
  simp

@[simp] theorem completed_one : (1 : E →L[ℂ] E).completion = 1 := by
  apply completion_map_ext
  intro x
  simp

/-- Completion does not change an operator norm. -/
@[simp] theorem completed_norm (f : E →L[ℂ] F) : ‖f.completion‖ = ‖f‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le f.completion.continuous.norm (continuous_const.mul continuous_norm)
    | ih x => simpa using f.le_opNorm x
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa using f.completion.le_opNorm (x : UniformSpace.Completion E)
end CompletionMaps

abbrev TensorHilbert (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] := UniformSpace.Completion (E ⊗[ℂ] F)

section TensorOperators
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def completedTensorMap (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    TensorHilbert E F →L[ℂ] TensorHilbert E F := (TensorProduct.mapL U V).completion

@[simp] theorem completedTensorMap_coe (U : E →L[ℂ] E) (V : F →L[ℂ] F)
    (z : E ⊗[ℂ] F) : completedTensorMap U V z = (TensorProduct.mapL U V z : TensorHilbert E F) :=
  ContinuousLinearMap.completion_apply_coe _ _

@[simp] theorem tensorMap_one : TensorProduct.mapL (1 : E →L[ℂ] E) (1 : F →L[ℂ] F) = 1 := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp] theorem completedTensorMap_one : completedTensorMap (1 : E →L[ℂ] E) (1 : F →L[ℂ] F) = 1 := by
  simp [completedTensorMap]

@[simp] theorem completedTensorMap_mul (U U' : E →L[ℂ] E) (V V' : F →L[ℂ] F) :
    completedTensorMap (U * U') (V * V') = completedTensorMap U V * completedTensorMap U' V' := by
  change (TensorProduct.mapL (U.comp U') (V.comp V')).completion = _
  rw [TensorProduct.mapL_comp, completed_comp]
  rfl

@[simp] theorem completedTensorMap_add_left (U U' : E →L[ℂ] E) (V : F →L[ℂ] F) :
    completedTensorMap (U+U') V = completedTensorMap U V + completedTensorMap U' V := by
  simp [completedTensorMap, TensorProduct.mapL_add_left]

@[simp] theorem completedTensorMap_add_right (U : E →L[ℂ] E) (V V' : F →L[ℂ] F) :
    completedTensorMap U (V+V') = completedTensorMap U V + completedTensorMap U V' := by
  simp [completedTensorMap, TensorProduct.mapL_add_right]

@[simp] theorem completedTensorMap_smul_left (c : ℂ) (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    completedTensorMap (c • U) V = c • completedTensorMap U V := by
  simp [completedTensorMap, TensorProduct.mapL_smul_left]

@[simp] theorem completedTensorMap_smul_right (c : ℂ) (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    completedTensorMap U (c • V) = c • completedTensorMap U V := by
  simp [completedTensorMap, TensorProduct.mapL_smul_right]

@[simp] theorem completedTensorMap_zero_left (V : F →L[ℂ] F) : completedTensorMap (0 : E →L[ℂ] E) V = 0 := by
  simp [completedTensorMap]

@[simp] theorem completedTensorMap_zero_right (U : E →L[ℂ] E) : completedTensorMap U (0 : F →L[ℂ] F) = 0 := by
  simp [completedTensorMap]

/-- The elementary tensor bound, including unequal varying dimensions. -/
theorem completedTensorMap_norm_le (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    ‖completedTensorMap U V‖ ≤ ‖U‖ * ‖V‖ := by
  rw [completedTensorMap, completed_norm]
  exact TensorProduct.norm_mapL_le _ _

variable [CompleteSpace E] [CompleteSpace F]

/-- Adjoint compatibility proved on the dense tensor product, not by assuming it complete. -/
@[simp] theorem completedTensorMap_star (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    completedTensorMap (star U) (star V) = star (completedTensorMap U V) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    induction y using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih y =>
      simp only [completedTensorMap_coe, UniformSpace.Completion.inner_coe]
      induction x using TensorProduct.inductionOn with
      | add x x' hx hx' => simp only [map_add, inner_add_left, hx, hx']
      | tmul a b =>
        induction y using TensorProduct.inductionOn with
        | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']
        | tmul a' b' =>
          simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul, ContinuousLinearMap.star_eq_adjoint]
          rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]

/-- The two commuting unital coordinate tensor embeddings. -/
def tensorLeftHom : (E →L[ℂ] E) →⋆ₐ[ℂ] (TensorHilbert E F →L[ℂ] TensorHilbert E F) where
  toFun U := completedTensorMap U 1
  map_zero' := by simp
  map_one' := completedTensorMap_one
  map_add' := by intros; simp
  map_mul' U V := by simpa using completedTensorMap_mul U V (1 : F →L[ℂ] F) 1
  commutes' c := by
    change completedTensorMap (c • 1) 1 = c • 1
    simp
  map_star' U := by simpa using completedTensorMap_star U (1 : F →L[ℂ] F)

def tensorRightHom : (F →L[ℂ] F) →⋆ₐ[ℂ] (TensorHilbert E F →L[ℂ] TensorHilbert E F) where
  toFun V := completedTensorMap 1 V
  map_zero' := by simp
  map_one' := completedTensorMap_one
  map_add' := by intros; simp
  map_mul' U V := by simpa using completedTensorMap_mul (1 : E →L[ℂ] E) 1 U V
  commutes' c := by
    change completedTensorMap 1 (c • 1) = c • 1
    simp
  map_star' U := by simpa using completedTensorMap_star (1 : E →L[ℂ] E) U

theorem tensorLeftRight_mul (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    tensorLeftHom U * tensorRightHom V = completedTensorMap U V := by
  change completedTensorMap U 1 * completedTensorMap 1 V = _
  rw [← completedTensorMap_mul, mul_one, one_mul]

theorem tensorLeftRight_commute (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    Commute (tensorLeftHom U) (tensorRightHom V) := by
  change completedTensorMap U 1 * completedTensorMap 1 V = completedTensorMap 1 V * completedTensorMap U 1
  simp only [← completedTensorMap_mul, mul_one, one_mul]
end TensorOperators
end NuclearUltrapower

end
end
end
end
end
end

end OAI
