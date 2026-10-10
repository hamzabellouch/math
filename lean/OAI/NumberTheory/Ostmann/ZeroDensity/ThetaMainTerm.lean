import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import OAI.NumberTheory.Ostmann.ZeroDensity.PrimePartialSummation

namespace OAI

/-! # The exceptional theta term and its harmonic density

Differentiating the published theta main term cancels its factor `β`.
The corresponding harmonic density is retained exactly.
-/

namespace Ostmann

open MeasureTheory

noncomputable def thetaMainTerm (φ χ β x : ℝ) : ℝ :=
  (x - χ * x ^ β / β) / φ

noncomputable def thetaMainDensity (φ χ β x : ℝ) : ℝ :=
  (1 - χ * x ^ (β - 1)) / φ

theorem hasDerivAt_thetaMainTerm (φ χ β : ℝ) (hβ : β ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaMainTerm φ χ β) (thetaMainDensity φ χ β x) x := by
  have h := ((hasDerivAt_id x).sub
    (((Real.hasDerivAt_rpow_const (p := β) (Or.inl hx.ne')).const_mul χ).div_const β)).div_const φ
  change HasDerivAt (fun y : ℝ => (y - χ * y ^ β / β) / φ)
    ((1 - χ * (β * x ^ (β - 1)) / β) / φ) x at h
  change HasDerivAt (fun y : ℝ => (y - χ * y ^ β / β) / φ)
    ((1 - χ * x ^ (β - 1)) / φ) x
  have he : (1 - χ * (β * x ^ (β - 1)) / β) / φ =
      (1 - χ * x ^ (β - 1)) / φ := by
    congr 1
    field_simp
  exact he ▸ h

theorem continuousOn_thetaMainDensity (φ χ β : ℝ) {u v : ℝ} (hu : 0 < u) :
    ContinuousOn (thetaMainDensity φ χ β) (Set.Icc u v) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hu hx.1)
  exact ((continuousAt_const.sub ((Real.continuousAt_rpow_const x (β - 1)
    (Or.inl hx0)).const_mul χ)).div_const φ).continuousWithinAt

theorem thetaMain_harmonic_integral (φ χ β : ℝ) (hβ : β ≠ 0)
    {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    (∫ t in Set.Ioc u v, primeHarmonicWeight t * thetaMainDensity φ χ β t) =
      primeHarmonicWeight v * thetaMainTerm φ χ β v -
      primeHarmonicWeight u * thetaMainTerm φ χ β u -
        ∫ t in Set.Ioc u v, primeHarmonicDerivative t * thetaMainTerm φ χ β t := by
  have hi1 : IntervalIntegrable primeHarmonicDerivative volume u v :=
    (continuousOn_primeHarmonicDerivative hu).intervalIntegrable_of_Icc huv
  have hi2 : IntervalIntegrable (thetaMainDensity φ χ β) volume u v :=
    (continuousOn_thetaMainDensity φ χ β (lt_trans zero_lt_one hu)).intervalIntegrable_of_Icc huv
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => hasDerivAt_primeHarmonicWeight
      (lt_of_lt_of_le hu ((Set.uIcc_of_le huv) ▸ hx).1))
    (fun x hx => hasDerivAt_thetaMainTerm φ χ β hβ
      (lt_trans zero_lt_one (lt_of_lt_of_le hu ((Set.uIcc_of_le huv) ▸ hx).1))) hi1 hi2
  simpa only [intervalIntegral.integral_of_le huv] using h

end Ostmann

end OAI
