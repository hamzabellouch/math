import OAI.NumberTheory.JointDickman.Probability.CompactTensorApproximation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

namespace OAI

/-! # Smooth separated factors for compact polynomial approximation -/

namespace JointDickman
open Finset
open scoped SchwartzMap

noncomputable def tensorBoxBump : ContDiffBump (9/4 : ℝ) where
  rIn := 7/4
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem tensorBoxBump_one {x : ℝ} (hx : x ∈ Set.Icc (1/2) 4) : tensorBoxBump x = 1 := by
  apply tensorBoxBump.one_of_mem_closedBall
  change dist x (9/4 : ℝ) ≤ (7/4 : ℝ)
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith [hx.1,hx.2]

theorem tensorBoxBump_zero {x : ℝ} (hx : x ≤ 1/4 ∨ 17/4 < x) : tensorBoxBump x = 0 := by
  apply tensorBoxBump.zero_of_le_dist
  change (2 : ℝ) ≤ dist x (9/4 : ℝ)
  rw [Real.dist_eq]
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

noncomputable def tensorPowerFactor (n : ℕ) : 𝓢(ℝ,ℝ) :=
  (tensorBoxBump.hasCompactSupport.mul_left (f := fun x : ℝ => x^n)).toSchwartzMap
    ((contDiff_id.pow n).mul tensorBoxBump.contDiff)

theorem tensorPowerFactor_apply (n : ℕ) (x : ℝ) :
    tensorPowerFactor n x = x^n*tensorBoxBump x := rfl

theorem tensorPowerFactor_support (n : ℕ) (x : ℝ) (hx : x ≤ 1/4 ∨ 17/4 < x) :
    tensorPowerFactor n x = 0 := by rw [tensorPowerFactor_apply,tensorBoxBump_zero hx,mul_zero]

theorem schwartz_value_derivative_bounds (w : 𝓢(ℝ,ℝ)) :
    ∃ M D : ℝ, 0 ≤ M ∧ 0 ≤ D ∧ (∀ x, |w x| ≤ M) ∧
      (∀ x, |deriv w x| ≤ D) ∧ Continuous (deriv w) := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 w,
    SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℝ w),
    apply_nonneg _ _,apply_nonneg _ _,?_,?_,?_⟩
  · intro x
    simpa only [Real.norm_eq_abs] using SchwartzMap.norm_le_seminorm ℝ w x
  · intro x
    simpa only [Real.norm_eq_abs,SchwartzMap.derivCLM_apply] using
      SchwartzMap.norm_le_seminorm ℝ (SchwartzMap.derivCLM ℝ ℝ w) x
  · exact (SchwartzMap.derivCLM ℝ ℝ w).continuous

theorem tensor_polynomial_expansion (P : MvPolynomial (Fin 4) ℝ) (x y z s : ℝ) :
    MvPolynomial.eval ![x,y,z,s] P*tensorBoxBump x*tensorBoxBump y*tensorBoxBump z =
      ∑ d ∈ P.support, (P.coeff d*s^(d 3))*
        tensorPowerFactor (d 0) x*tensorPowerFactor (d 1) y*tensorPowerFactor (d 2) z := by
  rw [MvPolynomial.eval_eq']
  simp only [sum_mul]
  apply sum_congr rfl
  intro d _
  simp only [tensorPowerFactor_apply]
  simp [Fin.prod_univ_succ]
  ring

end JointDickman

end OAI
