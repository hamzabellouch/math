import Mathlib
import OAI.Analysis.LaughlinFock.Rotations

namespace OAI

/-! Rectangular Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open NormedSpace MeasureTheory Topology

section Exponential
open scoped Matrix.Norms.Operator

 

theorem matrix_exp_intertwiner {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (C : Matrix κ ι ℂ)
    (h : Y*C = C*X) : exp Y * C = C * exp X := by
  have hp (n : ℕ) : Y^n*C = C*X^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  have hL := (mulRightLinearMap κ ℂ C).toContinuousLinearMap.hasSum
    (exp_series_hasSum_exp' (𝕂:=ℂ) Y)
  have hR := (mulLeftLinearMap ι ℂ C).toContinuousLinearMap.hasSum
    (exp_series_hasSum_exp' (𝕂:=ℂ) X)
  simp only [LinearMap.coe_toContinuousLinearMap', mulRightLinearMap_apply,
    mulLeftLinearMap_apply, Matrix.smul_mul, Matrix.mul_smul, hp] at hL hR
  exact hL.unique hR

 

theorem matrix_intertwiner_generator_of_flow {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (C : Matrix κ ι ℂ)
    (h : ∀ t : ℝ, exp ((t:ℂ) • Y) * C = C * exp ((t:ℂ) • X)) :
    Y*C = C*X := by
  have he : (fun t : ℝ => exp (t • Y) * C) = (fun t : ℝ => C * exp (t • X)) := by
    funext t
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    exact h t
  have hL := (mulRightLinearMap κ ℂ C).toContinuousLinearMap.restrictScalars ℝ |>.hasFDerivAt
    |>.comp_hasDerivAt (0:ℝ) (hasDerivAt_exp_smul_const Y (0:ℝ))
  have hR := (mulLeftLinearMap ι ℂ C).toContinuousLinearMap.restrictScalars ℝ |>.hasFDerivAt
    |>.comp_hasDerivAt (0:ℝ) (hasDerivAt_exp_smul_const X (0:ℝ))
  change HasDerivAt (fun t : ℝ => exp (t • Y) * C) ((exp (0 • Y) * Y)*C) 0 at hL
  change HasDerivAt (fun t : ℝ => C * exp (t • X)) (C*(exp (0 • X)*X)) 0 at hR
  rw [he] at hL
  simpa only [zero_smul, exp_zero, Matrix.one_mul] using! hL.unique hR

end Exponential

section Groups
variable {J σ : Type*} {I : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]

 
def intertwinerSubgroup {i j : J} (C : Matrix (I j) (I i) ℂ) :
    Subgroup (UnitaryFamily I) where
  carrier := {g | (g j).val * C = C * (g i).val}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change (g j).val * C = C * (g i).val at hg
    change (h j).val * C = C * (h i).val at hh
    change ((g j).val * (h j).val) * C = C * ((g i).val * (h i).val)
    rw [Matrix.mul_assoc, hh, ← Matrix.mul_assoc, hg, Matrix.mul_assoc]
  inv_mem' := by
    intro g hg
    change (g j).val * C = C * (g i).val at hg
    have he := congrArg (fun A => ((g j)⁻¹).val * A * ((g i)⁻¹).val) hg
    change ((g j)⁻¹).val * C = C * ((g i)⁻¹).val
    have hj : ((g j)⁻¹).val * (g j).val = 1 := by
      exact congrArg Subtype.val (inv_mul_cancel (g j))
    have hi : (g i).val * ((g i)⁻¹).val = 1 := by
      exact congrArg Subtype.val (mul_inv_cancel (g i))
    have heL : ((g j)⁻¹).val * ((g j).val*C) * ((g i)⁻¹).val = C*((g i)⁻¹).val := by
      rw [← Matrix.mul_assoc ((g j)⁻¹).val (g j).val C, hj, Matrix.one_mul]
    have heR : ((g j)⁻¹).val * (C*(g i).val) * ((g i)⁻¹).val = ((g j)⁻¹).val*C := by
      rw [Matrix.mul_assoc ((g j)⁻¹).val (C*(g i).val), Matrix.mul_assoc C, hi, Matrix.mul_one]
    rw [heL, heR] at he
    exact he.symm

open scoped Matrix.Norms.Elementwise

theorem intertwinerSubgroup_isClosed {i j : J} (C : Matrix (I j) (I i) ℂ) :
    IsClosed (intertwinerSubgroup C : Set (UnitaryFamily I)) := by
  change IsClosed {g : UnitaryFamily I | (g j).val*C = C*(g i).val}
  apply isClosed_eq <;> fun_prop

 

theorem rotationGroup_intertwiner
    (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j) {i j : J}
    (C : Matrix (I j) (I i) ℂ) (hC : ∀ s, X s j*C = C*X s i)
    (g : rotationGroup X hX) : (g.val j).val*C = C*(g.val i).val := by
  have hle : rotationGroup X hX ≤ intertwinerSubgroup C := by
    apply Subgroup.topologicalClosure_minimal
    · apply (Subgroup.closure_le _).2
      rintro _ ⟨⟨s,t⟩,rfl⟩
      change exp ((t:ℂ) • X s j)*C = C*exp ((t:ℂ) • X s i)
      exact matrix_exp_intertwiner _ _ C (by simp only [Matrix.smul_mul, Matrix.mul_smul, hC s])
    · exact intertwinerSubgroup_isClosed C
  exact hle g.property

end Groups
end LaughlinFock
end

end OAI
