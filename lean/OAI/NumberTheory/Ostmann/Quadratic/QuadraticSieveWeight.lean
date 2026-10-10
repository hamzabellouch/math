import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveFinite

namespace OAI

/-! # The fixed nonnegative smoothing weight in Heath-Brown's argument -/

namespace Ostmann

open scoped SchwartzMap BigOperators

noncomputable def quadraticSieveBump : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

noncomputable def quadraticSieveWeight : 𝓢(ℝ, ℂ) :=
  (quadraticSieveBump.hasCompactSupport.comp_left
    (show Complex.ofReal 0 = 0 by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp quadraticSieveBump.contDiff)

theorem quadraticSieveWeight_apply (x : ℝ) :
    quadraticSieveWeight x = (quadraticSieveBump x : ℂ) := rfl

theorem quadraticSieveBump_nonneg (x : ℝ) : 0 ≤ quadraticSieveBump x :=
  quadraticSieveBump.nonneg

theorem quadraticSieveBump_le_one (x : ℝ) : quadraticSieveBump x ≤ 1 :=
  quadraticSieveBump.le_one

theorem quadraticSieveWeight_eq_one {x : ℝ} (hx : x ∈ Set.Icc 1 2) :
    quadraticSieveWeight x = 1 := by
  have hh : quadraticSieveBump x = 1 := quadraticSieveBump.one_of_mem_closedBall (by
    change |x - 3 / 2| ≤ 1 / 2
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2])
  rw [quadraticSieveWeight_apply, hh, Complex.ofReal_one]

theorem quadraticSieveBump_eq_zero {x : ℝ} (hx : x ≤ 1 / 2 ∨ 5 / 2 ≤ x) :
    quadraticSieveBump x = 0 := by
  apply quadraticSieveBump.zero_of_le_dist
  change 1 ≤ |x - 3 / 2|
  rcases hx with hx | hx
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

theorem quadraticSieveWeight_eq_zero {x : ℝ} (hx : x ≤ 1 / 2 ∨ 5 / 2 ≤ x) :
    quadraticSieveWeight x = 0 := by
  rw [quadraticSieveWeight_apply, quadraticSieveBump_eq_zero hx, Complex.ofReal_zero]

theorem quadraticSieveWeight_zero : quadraticSieveWeight 0 = 0 :=
  quadraticSieveWeight_eq_zero (Or.inl (by norm_num))

theorem quadraticSieveWeight_norm_le_one (x : ℝ) : ‖quadraticSieveWeight x‖ ≤ 1 := by
  rw [quadraticSieveWeight_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (quadraticSieveBump_nonneg x)]
  exact quadraticSieveBump_le_one x

end Ostmann

end OAI
