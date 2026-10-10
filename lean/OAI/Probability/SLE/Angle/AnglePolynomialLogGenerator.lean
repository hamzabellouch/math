import OAI.Probability.SLE.Angle.AnglePolynomialLogField
import OAI.Probability.SLE.Angle.AngleEigenPolynomials

namespace OAI

/-! Exact cancellation for the Green-weighted angular eigenfunctions in
the original Brownian driver and actual capacity-two coordinates. -/
noncomputable section
open Polynomial

namespace SLEExactGauge

lemma logPolynomialDensity_generator {κ : ℝ} (hκ : 0<κ) (c : ℝ) (P : ℝ[X])
    (q : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun r : ℂ × ℝ => logPolynomialDensity κ (codimension κ+c) (greenExponent κ) P r x) q
        (physicalLogLoewnerField (Real.sqrt κ*x) q)+
      (1/2:ℝ)*iteratedDeriv 2 (logPolynomialDensity κ (codimension κ+c) (greenExponent κ) P q) x =
    powerLogDensity κ (codimension κ+c) (greenExponent κ) q x*logClockRate κ q x*
      ((anglePolynomialGenerator κ P).eval (logCosine κ q x)+c*P.eval (logCosine κ q x)) := by
  have hH := shifted_green_generator hκ c q x
  have hC := logCosine_tilted_drift hκ q x
  have hV := logCosine_tilted_variance hκ.le q x
  rw [logPolynomialDensity_directional,logPolynomialDensity_second,
    (powerLogDensity_spatial_derivative κ (codimension κ+c) (greenExponent κ) q x).deriv]
  simp only [anglePolynomialGenerator,eval_sub,eval_mul,eval_C,eval_pow,eval_X,eval_one]
  linear_combination P.eval (logCosine κ q x)*hH +
    powerLogDensity κ (codimension κ+c) (greenExponent κ) q x*
      P.derivative.eval (logCosine κ q x)*hC +
    powerLogDensity κ (codimension κ+c) (greenExponent κ) q x*
      P.derivative.derivative.eval (logCosine κ q x)*hV

lemma logEigenDensity_generator_zero {κ : ℝ} (hκ : 0<κ) (n : ℕ) (q : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun r : ℂ × ℝ => logPolynomialDensity κ
      (codimension κ+anglePolynomialEigenvalue κ n) (greenExponent κ) (angleEigenPolynomial κ n) r x) q
        (physicalLogLoewnerField (Real.sqrt κ*x) q)+
      (1/2:ℝ)*iteratedDeriv 2 (logPolynomialDensity κ
        (codimension κ+anglePolynomialEigenvalue κ n) (greenExponent κ) (angleEigenPolynomial κ n) q) x=0 := by
  rw [logPolynomialDensity_generator hκ,angleEigenPolynomial_eigen hκ]
  simp only [eval_mul,eval_neg,eval_C]
  ring

end SLEExactGauge

end

end OAI
