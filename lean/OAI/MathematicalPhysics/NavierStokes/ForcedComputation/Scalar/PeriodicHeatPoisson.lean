import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PeriodicHeatSeries
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatLattice
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

namespace OAI

/-! Poisson summation identifies the periodic heat Fourier series with the
actual Gaussian lattice sum used in the detector. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open scoped ContDiff BigOperators

theorem periodicHeatMoment_zero_gaussian {t : ℝ} (ht : 0 < t) (x : ℝ) :
    periodicHeatMoment 0 (t, x) =
      (Real.sqrt (4 * Real.pi * t) : ℂ)⁻¹ * (gaussianLattice t x : ℂ) := by
  let a : ℝ := 4 * Real.pi * t
  have ha : 0 < a := by dsimp only [a]; positivity
  have h := Complex.tsum_exp_neg_quadratic (a := (a : ℂ))
    (by simpa only [Complex.ofReal_re] using ha) (Complex.I * (x : ℂ))
  have hl : periodicHeatMoment 0 (t, x) =
      ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * (n : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * (Complex.I * (x : ℂ)) * (n : ℂ)) := by
    apply tsum_congr
    intro n
    simp only [heatMode, pow_zero, one_mul, heatModeLinear, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Complex.ofRealCLM_apply, Complex.real_smul,
      smul_eq_mul, a]
    congr 1
    push_cast
    ring
  have hr : (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) / (a : ℂ) *
      ((n : ℂ) + Complex.I * (Complex.I * (x : ℂ))) ^ 2)) =
      (gaussianLattice t x : ℂ) := by
    calc
      _ = ∑' n : ℤ, (Real.exp (-((x + ((-n : ℤ) : ℝ)) ^ 2) / (4 * t)) : ℂ) := by
        apply tsum_congr
        intro n
        rw [Complex.ofReal_exp]
        congr 1
        simp only [a, Int.cast_neg]
        push_cast
        simp only [← mul_assoc Complex.I Complex.I, Complex.I_mul_I, neg_one_mul]
        field_simp [ht.ne', Real.pi_ne_zero]
        ring
      _ = ∑' n : ℤ, (Real.exp (-((x + (n : ℝ)) ^ 2) / (4 * t)) : ℂ) :=
        (Equiv.neg ℤ).tsum_eq (fun n : ℤ =>
          (Real.exp (-((x + (n : ℝ)) ^ 2) / (4 * t)) : ℂ))
      _ = _ := (Complex.ofReal_tsum _).symm
  rw [hl, h, hr]
  congr 1
  rw [one_div]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]
  congr 1
  norm_num

end ForcedComputation.VelocityDetector

end

end OAI
