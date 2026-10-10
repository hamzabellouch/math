import Mathlib
import OAI.Analysis.HardSphere.Cutoffs.Regularize

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace ComplexRegularization

lemma differential_zero_formula (z w : ℂ) :
    differential 0 z w = ((inner ℝ z w / ‖z‖ : ℝ) : ℂ) := by
  simp [differential, div_eq_mul_inv, mul_comm]
  ring

lemma phase_differential_of_norm_eq (z w : ℂ)
    (he : ‖differential 0 z w‖ = ‖w‖) :
    w = z / (‖z‖ : ℂ) * differential 0 z w := by
  rw [differential_zero_formula] at he ⊢
  by_cases hz : z = 0
  · simp only [hz, norm_zero, Complex.ofReal_zero, div_zero, zero_mul] at he ⊢
    simpa only [eq_comm, norm_eq_zero] using he
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hs := congrArg (fun x : ℝ ↦ x^2) he
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow] at hs
  have hs' : (inner ℝ z w)^2 = ‖w‖^2 * ‖z‖^2 := (div_eq_iff (pow_ne_zero 2 hn)).mp hs
  have hp : w = (inner ℝ z w / ‖z‖^2) • z := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    apply (sq_eq_zero_iff).mp
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm (x := z)]
    field_simp
    nlinarith [hs']
  calc
    w = (inner ℝ z w / ‖z‖^2) • z := hp
    _ = z / (‖z‖ : ℂ) * ((inner ℝ z w / ‖z‖ : ℝ) : ℂ) := by
      simp only [Complex.real_smul]
      push_cast
      simp only [div_eq_mul_inv]
      ring

end ComplexRegularization

end
end
end

end OAI
