import OAI.Probability.InvariantIsing.Haar.HaarExponentialGradient

namespace OAI

/-! Dominated transport from positive polynomial truncations to exponential observables. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma haarExpPolynomial_test_integral_tendsto {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] (p : MatrixPolynomial N)
    (hp : ∀ U : SpecialOrthogonal N, 0 ≤ haarPolynomialValue p U)
    (F : ℝ → ℝ) (hF : Continuous F) :
    Tendsto (fun n : ℕ => ∫ U, F (haarPolynomialValue (haarExpPolynomial (n+1) p) U) ∂μ)
      atTop (𝓝 (∫ U, F (Real.exp (haarPolynomialValue p U)) ∂μ)) := by
  obtain ⟨B,hB⟩ := haarPolynomialValue_bound p
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn F (Icc 1 (Real.exp B)) from hF.continuousOn)
  apply tendsto_integral_of_dominated_convergence (fun _ => K)
    (fun n => (hF.comp (continuous_haarPolynomialValue _)).aestronglyMeasurable)
    (integrable_const K)
  · intro n
    apply ae_of_all
    intro U
    apply hK
    refine ⟨haarExpPolynomial_positive (n+1) p _ (hp U),?_⟩
    rw [haarPolynomialValue,haarExpPolynomial_eval]
    exact (positiveExpSum_le_exp (n+1) (hp U)).trans
      (Real.exp_le_exp.mpr ((le_abs_self _).trans (hB U)))
  · apply ae_of_all
    intro U
    apply hF.continuousAt.tendsto.comp
    have h := (positiveExpSum_tendsto (haarPolynomialValue p U)).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def,haarPolynomialValue,haarExpPolynomial_eval,positiveExpSum] using h

theorem haar_exp_polynomial_entropy_bound {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : MatrixPolynomial N) (hp : ∀ U : SpecialOrthogonal N, 0 ≤ haarPolynomialValue p U)
    (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ U : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) U ≤ C) :
    (∫ U, Real.exp (haarPolynomialValue p U)*Real.log (Real.exp (haarPolynomialValue p U)) ∂μ)-
      (∫ U, Real.exp (haarPolynomialValue p U) ∂μ)*
        Real.log (∫ U, Real.exp (haarPolynomialValue p U) ∂μ) ≤
      C*(∫ U, Real.exp (haarPolynomialValue p U) ∂μ)/(2*((N:ℝ)-2)) := by
  have hn (n : ℕ) :
      (∫ U, haarPolynomialValue (haarExpPolynomial (n+1) p) U*
        Real.log (haarPolynomialValue (haarExpPolynomial (n+1) p) U) ∂μ)-
      (∫ U, haarPolynomialValue (haarExpPolynomial (n+1) p) U ∂μ)*
        Real.log (∫ U, haarPolynomialValue (haarExpPolynomial (n+1) p) U ∂μ) ≤
      C*(∫ U, haarPolynomialValue (haarExpPolynomial (n+1) p) U ∂μ)/(2*((N:ℝ)-2)) := by
    obtain ⟨d,hd⟩ := exists_mem_haarPolynomialSpace (haarExpPolynomial (n+1) p)
    exact haarPolynomial_entropy_bound hN μ ⟨_,hd⟩ 1 C zero_lt_one
      (fun U => haarExpPolynomial_positive (n+1) p _ (hp U))
      (fun U => haarExpPolynomial_log_gradient_bound n p _ (hp U) C hC (hG U))
  have hm := haarExpPolynomial_test_integral_tendsto μ p hp id continuous_id
  simp only [id_eq] at hm
  have he := haarExpPolynomial_test_integral_tendsto μ p hp (fun x => x*Real.log x) Real.continuous_mul_log
  exact le_of_tendsto_of_tendsto (he.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hm))
    ((hm.const_mul C).div_const (2*((N:ℝ)-2))) (Eventually.of_forall hn)

end InvariantIsing

end

end OAI
