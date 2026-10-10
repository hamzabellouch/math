import OAI.Probability.InvariantIsing.Haar.HaarExponentialMomentBound

namespace OAI

/-! Removing the positivity normalization from polynomial exponential-moment bounds. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
namespace InvariantIsing

lemma haarPolynomialDerivation_C {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) :
    matrixPolynomialDerivation A (MvPolynomial.C c) = 0 :=
  (matrixPolynomialDerivation A).map_algebraMap c

lemma haarPolynomialGamma_add_C {N : ℕ} (p : MatrixPolynomial N) (c : ℝ) :
    haarPolynomialGamma (p+MvPolynomial.C c) (p+MvPolynomial.C c) = haarPolynomialGamma p p := by
  simp only [haarPolynomialGamma,map_add,haarPolynomialDerivation_C,add_zero]

lemma haarPolynomialMoment_add_C {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    (p : MatrixPolynomial N) (c t : ℝ) :
    haarPolynomialMoment μ (p+MvPolynomial.C c) t = Real.exp (t*c)*haarPolynomialMoment μ p t := by
  unfold haarPolynomialMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all μ fun U => by
    simp only [haarPolynomialValue,map_add,matrixPolynomialEval_C]
    rw [← Real.exp_add]
    congr 1
    ring

theorem haarPolynomialMoment_log_bound {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : MatrixPolynomial N) (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ U : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) U ≤ C)
    {t : ℝ} (ht : 0 < t) :
    Real.log (haarPolynomialMoment μ p t) ≤
      (∫ U, haarPolynomialValue p U ∂μ)*t+C/(2*((N:ℝ)-2))*t^2 := by
  obtain ⟨B,hB⟩ := haarPolynomialValue_bound p
  have hpq (U : SpecialOrthogonal N) : 0 ≤ haarPolynomialValue (p+MvPolynomial.C B) U := by
    simp only [haarPolynomialValue,map_add,matrixPolynomialEval_C]
    have hh := hB U
    rw [Real.norm_eq_abs] at hh
    dsimp only [haarPolynomialValue] at hh
    linarith [(abs_le.mp hh).1]
  have hGq (U : SpecialOrthogonal N) :
      haarPolynomialValue (haarPolynomialGamma (p+MvPolynomial.C B) (p+MvPolynomial.C B)) U ≤ C := by
    rw [haarPolynomialGamma_add_C]
    exact hG U
  have h := haarPolynomialMoment_log_bound_of_nonneg hN μ (p+MvPolynomial.C B) hpq C hC hGq ht
  rw [haarPolynomialMoment_add_C,Real.log_mul (Real.exp_ne_zero _) (haarPolynomialMoment_pos μ p t).ne',
    Real.log_exp] at h
  have hm : (∫ U, haarPolynomialValue (p+MvPolynomial.C B) U ∂μ) =
      (∫ U, haarPolynomialValue p U ∂μ)+B := by
    have he (U : SpecialOrthogonal N) : haarPolynomialValue (p+MvPolynomial.C B) U = haarPolynomialValue p U+B := by
      simp only [haarPolynomialValue,map_add,matrixPolynomialEval_C]
    simp_rw [he]
    rw [integral_add (haarPolynomialValue_integrable p μ) (integrable_const B)]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  rw [hm] at h
  nlinarith

end InvariantIsing

end

end OAI
