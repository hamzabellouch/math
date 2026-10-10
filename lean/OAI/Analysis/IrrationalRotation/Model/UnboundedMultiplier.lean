import OAI.Analysis.IrrationalRotation.Model.WeightedShift
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

noncomputable section
open scoped ENNReal
namespace Invariant233.WeightedShift

def multiplierDomain (h : ℤ → ℂ) : Submodule ℂ Hilbert where
  carrier := {ξ | Memℓp (fun k => h k * ξ k) 2}
  zero_mem' := by simpa using (zero_mem_ℓp' : Memℓp (fun _ : ℤ => (0 : ℂ)) 2)
  add_mem' := by
    intro ξ η hξ hη
    change Memℓp (fun k => h k * (ξ k + η k)) 2
    convert hξ.add hη using 1
    funext k
    exact mul_add _ _ _
  smul_mem' := by
    intro c ξ hξ
    simpa only [Set.mem_ofPred_eq, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm] using hξ.const_mul c

def multiplier (h : ℤ → ℂ) : multiplierDomain h →ₗ[ℂ] Hilbert where
  toFun ξ := ⟨fun k => h k * ξ.val k, ξ.property⟩
  map_add' ξ η := by ext k; exact mul_add _ _ _
  map_smul' c ξ := by ext k; exact mul_left_comm _ _ _

def unboundedMultiplier (h : ℤ → ℂ) : Hilbert →ₗ.[ℂ] Hilbert :=
  ⟨multiplierDomain h, multiplier h⟩

def exponentialWeight (g : ℤ → ℝ) (hg : ∀ k, 0 ≤ g k) : Weight :=
  ⟨fun k => (Real.exp (-g k) : ℂ), memℓp_infty <| by
    refine ⟨1, ?_⟩
    rintro r ⟨k, rfl⟩
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg k)))⟩

end Invariant233.WeightedShift

end

end OAI
