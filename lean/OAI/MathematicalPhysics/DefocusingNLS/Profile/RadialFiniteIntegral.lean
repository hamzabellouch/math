import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed

namespace OAI

/-! Finite-time integral estimates for the exterior ODE continuation. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radial_finite_integral_hasDerivAt (g : ℝ → ℂ × ℂ) (hg : Continuous g) (t : ℝ) :
    HasDerivAt (fun r => ∫ s in 0..r, g s) (g t) t :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

theorem radial_finite_integral_weighted (η t C : ℝ) (hη : 0 < η) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (g : ℝ → ℂ × ℂ) (hg : ∀ s ∈ Icc 0 t, ‖g s‖ ≤ C*Real.exp (η*s)) :
    Real.exp (-η*t)*‖∫ s in 0..t, g s‖ ≤ C/η := by
  have hi : ‖∫ s in 0..t, g s‖ ≤ ∫ s in 0..t, C*Real.exp (η*s) := by
    apply intervalIntegral.norm_integral_le_of_norm_le ht
      (Filter.Eventually.of_forall (fun s hs => hg s ⟨hs.1.le,hs.2⟩))
    exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 t
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left Real.exp hη.ne',integral_exp] at hi
  simp only [mul_zero,Real.exp_zero,smul_eq_mul] at hi
  have he : Real.exp (-η*t)*Real.exp (η*t)=1 := by
    rw [← Real.exp_add]
    simp
  calc
    _ ≤ Real.exp (-η*t)*(C*(η⁻¹*(Real.exp (η*t)-1))) :=
      mul_le_mul_of_nonneg_left hi (Real.exp_nonneg _)
    _ = (C/η)*(1-Real.exp (-η*t)) := by linear_combination C/η*he
    _ ≤ C/η := mul_le_of_le_one_right (div_nonneg hC hη.le) (by linarith [Real.exp_pos (-η*t)])

end DefocusingNLS

end OAI
