import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoordinateLieBrackets
import Mathlib.Algebra.Lie.Nilpotent

namespace OAI

/-! # A uniform nilpotence exponent for every coordinate adjoint -/

namespace PolycyclicRecognition

open Module LieModule

/-- Coordinate adjoints are uniformly nilpotent at any index at which the
actual lower central series vanishes. -/
theorem basisBracket_pow_eq_zero
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n k : ℕ}
    (b : Basis (Fin n) ℝ L) (hk : lowerCentralSeries ℝ L L k = ⊥)
    (x : Fin n → ℝ) : (basisBracket b x) ^ k = 0 := by
  have hiter (j : ℕ) (y : Fin n → ℝ) :
      ((basisBracket b x) ^ j) y =
        b.equivFun ((toEnd ℝ L L (b.equivFun.symm x))^[j] (b.equivFun.symm y)) := by
    induction j generalizing y with
    | zero =>
      change y = b.equivFun (b.equivFun.symm y)
      exact (b.equivFun.apply_symm_apply y).symm
    | succ j ih =>
      rw [pow_succ, mul_apply_eq_comp, ih]
      simp only [basisBracket_apply, LinearEquiv.symm_apply_apply,
        Function.iterate_succ_apply]
      rfl
  apply ContinuousLinearMap.ext
  intro y
  rw [hiter]
  have hz := iterate_toEnd_mem_lowerCentralSeries ℝ L L
    (b.equivFun.symm x) (b.equivFun.symm y) k
  rw [hk] at hz
  have heq : (toEnd ℝ L L (b.equivFun.symm x))^[k] (b.equivFun.symm y) = 0 :=
    hz
  rw [heq, map_zero]
  rfl

end PolycyclicRecognition

end OAI
