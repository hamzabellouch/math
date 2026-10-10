import OAI.Probability.InvariantIsing.Haar.HaarKernelApproximation
import OAI.Probability.InvariantIsing.Haar.HaarLipschitzGradient
import OAI.Probability.InvariantIsing.Haar.HaarUniformMomentLimit
import OAI.Probability.InvariantIsing.Haar.HaarPolynomialMomentShift

namespace OAI

/-! Exponential moments for all continuous Frobenius-Lipschitz observables. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter
open scoped Topology
namespace InvariantIsing

theorem haar_lipschitz_moment_bound {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) {t : ℝ} (ht : 0 < t) :
    (∫ U, Real.exp (t*f U) ∂μ) ≤
      Real.exp ((∫ U, f U ∂μ)*t+(4*L^2)/(2*((N:ℝ)-2))*t^2) := by
  have hN0 : 0 < N := by omega
  let p : ℕ → MatrixPolynomial N := haarKernelApprox μ f
  have hu := haarKernelApprox_uniform hN0 μ f hf L hL hLip
  obtain ⟨hmean,hmoment⟩ := haar_uniform_polynomial_integrals μ p f hf hu
  have hG (n : ℕ) (U : SpecialOrthogonal N) :
      haarPolynomialValue (haarPolynomialGamma (p n) (p n)) U ≤ 4*L^2 :=
    haarPolynomial_gamma_le_lipschitz (p n) L hL.le
      (haarKernelApprox_lipschitz hN0 μ f hf L hLip n) U
  have hbound (n : ℕ) : haarPolynomialMoment μ (p n) t ≤
      Real.exp ((∫ U, haarPolynomialValue (p n) U ∂μ)*t+(4*L^2)/(2*((N:ℝ)-2))*t^2) := by
    have hh := Real.exp_le_exp.mpr
      (haarPolynomialMoment_log_bound hN μ (p n) (4*L^2) (by positivity) (hG n) ht)
    rwa [Real.exp_log (haarPolynomialMoment_pos μ (p n) t)] at hh
  exact le_of_tendsto_of_tendsto (hmoment t)
    (Real.continuous_exp.continuousAt.tendsto.comp ((hmean.mul_const t).add_const _))
    (Eventually.of_forall hbound)

end InvariantIsing

end

end OAI
