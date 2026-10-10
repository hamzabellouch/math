import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

namespace OAI

/-! # Commutation through invertible linear factors -/

namespace PolycyclicRecognition
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem linear_commute_symm (e : V ≃ₗ[ℝ] V) (T : Module.End ℝ V)
    (h : Commute T e.toLinearMap) : Commute T e.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  change T (e.symm x) = e.symm (T x)
  apply e.injective
  rw [e.apply_symm_apply]
  have hh : T (e (e.symm x)) = e (T (e.symm x)) := LinearMap.congr_fun h.eq _
  rw [e.apply_symm_apply] at hh
  exact hh.symm

theorem linear_commute_of_mul_equiv_right (T F : Module.End ℝ V) (e : V ≃ₗ[ℝ] V)
    (he : Commute T e.toLinearMap) (h : Commute T (F * e.toLinearMap)) : Commute T F := by
  have hc := h.mul_right (linear_commute_symm e T he)
  have hh : F * e.toLinearMap * e.symm.toLinearMap = F := by
    apply LinearMap.ext
    intro x
    change F (e (e.symm x)) = F x
    rw [e.apply_symm_apply]
  rwa [hh] at hc

theorem linear_commute_conj (e : V ≃ₗ[ℝ] V) (T A : Module.End ℝ V)
    (he : Commute T e.toLinearMap) (hA : Commute T A) : Commute T (e.conjRingEquiv A) := by
  have hh : e.conjRingEquiv A = e.toLinearMap * A * e.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    rfl
  rw [hh]
  exact (he.mul_right hA).mul_right (linear_commute_symm e T he)

end PolycyclicRecognition

end OAI
