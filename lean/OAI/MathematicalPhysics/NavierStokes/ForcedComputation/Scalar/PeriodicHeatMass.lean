import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PeriodicHeatSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Unit mass for the periodic heat Fourier kernel. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open Set MeasureTheory
open scoped BigOperators

theorem heatFrequency_integral (n : ℤ) :
    (∫ y in Icc (0 : ℝ) 1,
      Complex.exp ((2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I) * y)) =
      if n = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  by_cases hn : n = 0
  · simp [hn]
  · rw [ite_eq_right hn, integral_exp_mul_complex (by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (Int.cast_ne_zero.mpr hn))
        Complex.I_ne_zero)]
    have he : Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I) = 1 := by
      have h := (Complex.exp_periodic.int_mul n) 0
      calc
        _ = Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :=
          congrArg Complex.exp (by ring)
        _ = 1 := by simpa only [Complex.exp_zero, zero_add] using h
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, he, sub_self, zero_div]

theorem heatMode_shift_factor (n : ℤ) (t x y : ℝ) :
    heatMode 0 n (t, x - y) = heatMode 0 n (t, x) *
      Complex.exp ((2 * (Real.pi : ℂ) * ((-n : ℤ) : ℂ) * Complex.I) * y) := by
  simp only [heatMode, pow_zero, one_mul, heatModeLinear, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', Complex.ofRealCLM_apply, Complex.real_smul, smul_eq_mul]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem periodicHeatMoment_integral {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ y in Icc (0 : ℝ) 1, periodicHeatMoment 0 (t, x - y)) = 1 := by
  have hs := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Icc (0 : ℝ) 1))
    (fun n : ℤ => fun _ : ℝ => heatModeBound 0 t n)
    (fun n => ((heatMode_smooth 0 n).continuous.comp
      (continuous_const.prodMk (continuous_const.sub continuous_id))).aestronglyMeasurable)
    (fun n => ae_of_all _ fun y => (heatMode_norm 0 n (t, x - y)).le)
    (ae_of_all _ fun _ => heatModeBound_summable 0 ht)
    continuous_const.integrableOn_Icc
    (ae_of_all _ fun y => (periodicHeatMoment_summable 0 (p := (t, x - y)) ht).hasSum)
  have he (n : ℤ) : (∫ y in Icc (0 : ℝ) 1, heatMode 0 n (t, x - y)) =
      if n = 0 then 1 else 0 := by
    simp_rw [heatMode_shift_factor]
    rw [integral_const_mul, heatFrequency_integral]
    by_cases hn : n = 0
    · subst n
      simp [heatMode, heatModeLinear]
    · simp [hn]
  have h := hs.tsum_eq
  change (∑' n : ℤ, ∫ y in Icc (0 : ℝ) 1, heatMode 0 n (t, x - y)) = _ at h
  simp only [he] at h
  simpa only [periodicHeatMoment, tsum_ite_eq, ite_true] using h.symm

end ForcedComputation.VelocityDetector

end

end OAI
