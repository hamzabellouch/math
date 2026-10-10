import Mathlib
import OAI.Probability.SKValue.Equations.ShiftedPairing
import OAI.Probability.SKValue.Evolution.BoundedSmooth

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma BoundedSmooth.iteratedDeriv {f : ℝ → ℝ} (hf : BoundedSmooth f) (n : ℕ) :
    BoundedSmooth (iteratedDeriv n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

lemma BoundedSmooth.heat_deriv {f : ℝ → ℝ} (hf : BoundedSmooth f) (h : ℝ) :
    _root_.deriv (heat h f)=heat h (_root_.deriv f) := by
  simpa only [iteratedDeriv_one] using heat_iteratedDeriv hf.smooth
    (fun n ↦ (hf.iteratedDeriv n).expGrowth) h 1

lemma standardGaussian_abs_integral_le_one : (∫ z : ℝ, |z| ∂standardGaussian)≤1 := by
  have hl : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) standardGaussian := HasLaw.id
  have hh := integral_abs_le_sqrt_integral_sq (gaussian_memLp hl 2 (by norm_num))
  rw [gaussian_second_moment hl,Real.sqrt_one] at hh
  exact hh

lemma BoundedSmooth.heat_kernel_deriv_bound {f : ℝ → ℝ} (hf : BoundedSmooth f)
    {A h : ℝ} (hA : 0≤A) (hb : ∀ x, |f x|≤A) (hh : 0<h) (x : ℝ) :
    |_root_.deriv (heat h f) x|≤A/Real.sqrt h := by
  have hs := Real.sqrt_pos.mpr hh
  have hid := gaussian_scale_deriv_eq
    (fun y ↦ (hf.smooth.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)) y).hasDerivAt)
    hf.deriv.smooth.continuous hf.expGrowth hf.deriv.expGrowth x (Real.sqrt h)
  have hi := hf.expGrowth.shift_mul_integrable hf.smooth.continuous.measurable x (Real.sqrt h)
  have hz : Integrable (fun z : ℝ ↦ |z| * A) standardGaussian := by
    exact ((memLp_id_gaussianReal' 1 (by norm_num)).integrable le_rfl).abs.mul_const A
  have hb' : |∫ z, z*f (x+Real.sqrt h*z) ∂standardGaussian|≤A := by
    calc
      _ ≤ ∫ z, |z*f (x+Real.sqrt h*z)| ∂standardGaussian := abs_integral_le_integral_abs
      _ ≤ ∫ z : ℝ, |z| * A ∂standardGaussian := by
        apply integral_mono_ae hi.abs hz
        filter_upwards [] with z
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)
      _ = (∫ z : ℝ, |z| ∂standardGaussian)*A := integral_mul_const _ _
      _ ≤ A := by nlinarith [standardGaussian_abs_integral_le_one]
  rw [hf.heat_deriv]
  apply (le_div_iff₀ hs).mpr
  rw [hid,abs_mul,abs_of_pos hs] at hb'
  exact (mul_comm _ _).trans_le hb'

end SKValue

end

end OAI
