import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace OAI
noncomputable section
namespace CuntzPureness
local instance groupRegularRepresentationDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
open scoped lp InnerProductSpace

def groupL2Perm {G : Type*} (e : G ≃ G) : ℓ²(G, ℂ) ≃ₗᵢ[ℂ] ℓ²(G, ℂ) where
  toFun x := ⟨fun g => x (e.symm g), memℓp_gen
    ((e.symm.summable_iff).mpr (x.property.summable (by norm_num)))⟩
  invFun x := ⟨fun g => x (e g), memℓp_gen
    ((e.summable_iff).mpr (x.property.summable (by norm_num)))⟩
  left_inv x := by ext g; simp
  right_inv x := by ext g; simp
  map_add' x y := by ext g; rfl
  map_smul' c x := by ext g; rfl
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun g => ‖x g‖ ^ (2 : ENNReal).toReal)

variable {G : Type*} [Group G]
abbrev GroupL2 (G : Type*) := ℓ²(G, ℂ)
abbrev GroupOperator (G : Type*) := GroupL2 G →L[ℂ] GroupL2 G

def groupLeft (g : G) : GroupOperator G := (groupL2Perm (Equiv.mulLeft g)).toContinuousLinearEquiv

def groupRight (g : G) : GroupOperator G := (groupL2Perm (Equiv.mulRight g⁻¹)).toContinuousLinearEquiv

@[simp] lemma groupLeft_apply (g h : G) (x : GroupL2 G) : groupLeft g x h = x (g⁻¹*h) := rfl
@[simp] lemma groupRight_apply (g h : G) (x : GroupL2 G) : groupRight g x h = x (h*g) := by simp [groupRight, groupL2Perm]

@[simp] lemma groupLeft_one : groupLeft (1 : G) = 1 := by ext x h; simp
@[simp] lemma groupLeft_mul (g h : G) : groupLeft (g*h) = groupLeft g * groupLeft h := by
  ext x k; simp [mul_assoc]
@[simp] lemma groupRight_one : groupRight (1 : G) = 1 := by ext x h; simp
@[simp] lemma groupRight_mul (g h : G) : groupRight (g*h) = groupRight g * groupRight h := by
  ext x k; simp [mul_assoc]

@[simp] lemma groupLeft_star (g : G) : star (groupLeft g) = groupLeft g⁻¹ := by
  change ContinuousLinearMap.adjoint ((groupL2Perm (Equiv.mulLeft g)) : GroupOperator G) = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  ext x h
  change x (g*h) = x (g⁻¹⁻¹*h)
  simp

@[simp] lemma groupRight_star (g : G) : star (groupRight g) = groupRight g⁻¹ := by
  change ContinuousLinearMap.adjoint ((groupL2Perm (Equiv.mulRight g⁻¹)) : GroupOperator G) = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  ext x h
  change x (h*g⁻¹) = x (h*g⁻¹⁻¹⁻¹)
  simp

lemma groupLeft_commute_right (g h : G) : Commute (groupLeft g) (groupRight h) := by
  ext x k; simp [mul_assoc]

def groupLeftUnitary : G →* unitary (GroupOperator G) where
  toFun g := ⟨groupLeft g, by
    constructor <;> simp [← groupLeft_mul]⟩
  map_one' := Subtype.ext groupLeft_one
  map_mul' g h := Subtype.ext (groupLeft_mul g h)

def groupVacuum : GroupL2 G := lp.single 2 1 1

lemma groupVacuum_norm : ‖groupVacuum (G := G)‖ = 1 := by
  classical
  simp [groupVacuum, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

lemma groupLeft_vacuum (g : G) : groupLeft g groupVacuum = lp.single 2 g 1 := by
  classical
  ext h
  simp [groupVacuum, lp.single_apply, Pi.single_apply, inv_mul_eq_one, eq_comm]

lemma groupRight_vacuum (g : G) : groupRight g groupVacuum = lp.single 2 g⁻¹ 1 := by
  classical
  ext h
  simp [groupVacuum, lp.single_apply, Pi.single_apply, mul_eq_one_iff_eq_inv]

lemma groupVacuum_inner (x : GroupL2 G) : ⟪groupVacuum, x⟫_ℂ = x 1 := by
  classical
  simp [groupVacuum, lp.inner_single_left]
end CuntzPureness

end

end OAI
