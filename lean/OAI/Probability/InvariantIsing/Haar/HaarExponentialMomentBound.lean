import OAI.Probability.InvariantIsing.Haar.HaarPolynomialMoment

namespace OAI

/-! Gaussian exponential-moment bounds for nonnegative polynomial observables. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomialGamma_scaled_value {N : ℕ} (p : MatrixPolynomial N) (c : ℝ)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (haarPolynomialGamma (c • p) (c • p)) =
      c^2*matrixPolynomialEval M (haarPolynomialGamma p p) := by
  simp only [haarPolynomialGamma,Derivation.map_smul_of_tower,map_sum,map_mul,map_smul,
    smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem haarPolynomialMoment_log_bound_of_nonneg {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : MatrixPolynomial N) (hp : ∀ U : SpecialOrthogonal N, 0 ≤ haarPolynomialValue p U)
    (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ U : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) U ≤ C)
    {t : ℝ} (ht : 0 < t) :
    Real.log (haarPolynomialMoment μ p t) ≤
      (∫ U, haarPolynomialValue p U ∂μ)*t+C/(2*((N:ℝ)-2))*t^2 := by
  have hE (s : ℝ) (hs : 0 < s) :
      s*haarPolynomialMomentDerivative μ p s-
        haarPolynomialMoment μ p s*Real.log (haarPolynomialMoment μ p s) ≤
      (C/(2*((N:ℝ)-2)))*s^2*haarPolynomialMoment μ p s := by
    have hscaled (U : SpecialOrthogonal N) : haarPolynomialValue (s • p) U = s*haarPolynomialValue p U := by
      simp only [haarPolynomialValue,map_smul,smul_eq_mul]
    have hp' (U : SpecialOrthogonal N) : 0 ≤ haarPolynomialValue (s • p) U := by
      rw [hscaled]
      exact mul_nonneg hs.le (hp U)
    have hG' (U : SpecialOrthogonal N) :
        haarPolynomialValue (haarPolynomialGamma (s • p) (s • p)) U ≤ C*s^2 := by
      rw [haarPolynomialValue,haarPolynomialGamma_scaled_value]
      have hh := mul_le_mul_of_nonneg_left (hG U) (sq_nonneg s)
      simpa only [haarPolynomialValue,mul_comm] using hh
    have he := haar_exp_polynomial_entropy_bound hN μ (s • p) hp' (C*s^2)
      (mul_nonneg hC (sq_nonneg s)) hG'
    simp_rw [hscaled,Real.log_exp] at he
    have hi : (∫ U, Real.exp (s*haarPolynomialValue p U)*(s*haarPolynomialValue p U) ∂μ) =
        s*haarPolynomialMomentDerivative μ p s := by
      rw [haarPolynomialMomentDerivative,← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all μ fun U => by ring
    rw [hi] at he
    change s*haarPolynomialMomentDerivative μ p s-
      haarPolynomialMoment μ p s*Real.log (haarPolynomialMoment μ p s) ≤
      C*s^2*haarPolynomialMoment μ p s/(2*((N:ℝ)-2)) at he
    linear_combination he
  have hh := log_moment_le_of_entropy (haarPolynomialMoment μ p)
    (haarPolynomialMomentDerivative μ p) (C/(2*((N:ℝ)-2)))
    (haarPolynomialMoment_pos μ p) (haarPolynomialMoment_zero μ p)
    (haarPolynomialMoment_hasDerivAt μ p) hE ht
  simpa only [haarPolynomialMomentDerivative_zero] using hh

end InvariantIsing

end

end OAI
