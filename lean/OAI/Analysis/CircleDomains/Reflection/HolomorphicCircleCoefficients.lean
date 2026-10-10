import OAI.Analysis.CircleDomains.Sobolev.ExteriorDerivativeMean
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Fourier.AddCircle

namespace OAI

/-! Exact circle coefficients of a holomorphic disk function. This is
Cauchy's formula in the Fourier normalization used for square integrals. -/
open Set Filter Function Metric Real MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def diskTaylorCoefficient (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

lemma circleAverage_inv_pow_mul {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall 0 r)) (n : ℕ) :
    circleAverage (fun z => (z^n)⁻¹ * f z) 0 r = diskTaylorCoefficient f n := by
  rw [circleAverage_eq_circleIntegral hr.ne']
  have he : (fun z : ℂ => (z-0)⁻¹ • ((z^n)⁻¹ * f z)) =
      (fun z : ℂ => (1/(z-0)^(n+1)) • f z) := by
    funext z
    simp only [sub_zero, smul_eq_mul, one_div, pow_succ, mul_inv_rev]
    ring
  rw [he, hf.circleIntegral_one_div_sub_center_pow_smul hr n]
  dsimp only [diskTaylorCoefficient]
  rw [smul_eq_mul, smul_eq_mul, div_eq_mul_inv]
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

lemma fourier_negative_eq_circle_inv_pow {r T : ℝ} (hT : T = 2*Real.pi)
    (hr : 0 < r) (n : ℕ) (θ : ℝ) :
    fourier (-(n : ℤ)) (θ : AddCircle T) =
      (r : ℂ)^n * (circleMap 0 r θ ^ n)⁻¹ := by
  rw [fourier_coe_apply, hT]
  have harg : (2 * (Real.pi : ℂ) * Complex.I * (-(n : ℤ) : ℤ) * θ / (2*Real.pi : ℝ)) =
      -((n : ℂ) * ((θ : ℂ)*Complex.I)) := by
    push_cast
    field_simp
  rw [harg, Complex.exp_neg, Complex.exp_nat_mul]
  rw [circleMap_zero, mul_pow, mul_inv_rev]
  have hn : (r : ℂ)^n ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne')
  field_simp

lemma holomorphic_circle_fourierCoefficient {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (closedBall 0 r)) (n : ℕ) :
    fourierCoeffOn (show (0 : ℝ) < 2*Real.pi by positivity)
      (fun θ => f (circleMap 0 r θ)) (n : ℤ) =
      (r : ℂ)^n * diskTaylorCoefficient f n := by
  rw [fourierCoeffOn_eq_integral]
  simp_rw [fourier_negative_eq_circle_inv_pow (sub_zero (2*Real.pi)) hr n]
  simp only [smul_eq_mul, mul_assoc]
  rw [intervalIntegral.integral_const_mul, ← circleAverage_inv_pow_mul hr hf n]
  simp only [sub_zero, one_div, circleAverage, Complex.real_smul]
  ring

end CircleDomainRigidity

end

end OAI
