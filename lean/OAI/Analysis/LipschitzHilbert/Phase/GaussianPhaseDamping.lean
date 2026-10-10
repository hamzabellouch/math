import OAI.Analysis.LipschitzHilbert.Phase.SimplexTubeInterpolation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

/-! Gaussian damping of the finite shift parameters. Its exact norm
removes the crude exp(C√L) growth outside the imaginary ball of radius L². -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
variable {ι : Type*} [Fintype ι]

def gaussianPhaseDamping (z : ι → ℂ) : ℂ := Complex.exp (∑ i, z i^2)

theorem gaussianPhaseDamping_norm (a eta : ι → ℝ) :
    ‖gaussianPhaseDamping (phaseTubePoint a eta)‖ =
      Real.exp ((∑ i, (a i)^2)-(∑ i, (eta i)^2)) := by
  rw [gaussianPhaseDamping,Complex.norm_exp]
  congr 1
  rw [← Finset.sum_sub_distrib]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [phaseTubePoint,pow_two,Complex.mul_re]

theorem gaussianPhaseDamping_affine_entire (a b eta : ι → ℝ) :
    Differentiable ℂ (fun z => gaussianPhaseDamping (phaseTubeLine a b eta z)) := by
  unfold gaussianPhaseDamping
  apply Differentiable.cexp
  apply Differentiable.fun_sum
  intro i _
  dsimp only [phaseTubeLine]
  fun_prop

theorem gaussianPhaseDamping_simplex_le (a eta : ι → ℝ) (mu : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = mu) :
    ‖gaussianPhaseDamping (phaseTubePoint a eta)‖ ≤
      Real.exp (mu^2-∑ i, (eta i)^2) := by
  rw [gaussianPhaseDamping_norm]
  apply Real.exp_le_exp.mpr
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := a) (fun i _ => ha i)
  rw [hsum] at h
  linarith

theorem eventually_gaussian_imaginary_tail (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ mu r : ℝ, 0 ≤ mu → mu ≤ 1 → L^2 ≤ r →
      (1+r)*Real.exp (mu^2-r^2+C*Real.sqrt L) ≤ 1 := by
  filter_upwards [eventually_ge_atTop (max 2 (C^2))] with L hL
  intro mu r hmu hmu1 hr
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 ≤ L := by linarith
  have hCsq : C^2 ≤ L := (le_max_right _ _).trans hL
  have hCp : C ≤ Real.sqrt L := (Real.le_sqrt hC hL0).mpr hCsq
  have hsqrt : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hCL : C*Real.sqrt L ≤ L := by nlinarith [Real.sq_sqrt hL0]
  have hr4 : 4 ≤ r := by nlinarith
  have hLr : L ≤ r := by nlinarith
  have hmu2 : mu^2 ≤ 1 := by nlinarith
  have he : r+(mu^2-r^2+C*Real.sqrt L) ≤ 0 := by nlinarith
  calc
    _ ≤ Real.exp r*Real.exp (mu^2-r^2+C*Real.sqrt L) :=
      mul_le_mul_of_nonneg_right (by simpa only [add_comm] using Real.add_one_le_exp r)
        (Real.exp_pos _).le
    _ = Real.exp (r+(mu^2-r^2+C*Real.sqrt L)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr he
    _ = 1 := Real.exp_zero

end LipschitzHilbert

end

end OAI
