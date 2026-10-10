import OAI.Probability.SLE.Angle.AngleEigenNorm
import OAI.Probability.SLE.Angle.TargetAngleLaw

namespace OAI

/-! Match the polynomial pairing to the exact angle probability measure
appearing in the prescribed coefficients. -/
noncomputable section
open Polynomial Set _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ENNReal

namespace SLEExactGauge

lemma anglePolynomialInner_eq_setIntegral (κ : ℝ) (p q : ℝ[X]) :
    anglePolynomialInner κ p q=∫ θ in Ioo (0:ℝ) Real.pi,
      Real.sin θ^(4*Target.a κ)*anglePolynomialTest p θ*anglePolynomialTest q θ := by
  rw [anglePolynomialInner,intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_Ioc_eq_integral_Ioo]

lemma angle_normalizer_eq_norm {κ : ℝ} (hκ : 0<κ) :
    ((volume.restrict (Ioo (0:ℝ) Real.pi)).withDensity
      (fun θ => ENNReal.ofReal (Real.sin θ^(4*Target.a κ)))) univ=
        ENNReal.ofReal (angleEigenSquareNorm κ 0) := by
  have hi := anglePolynomialInner_integrable hκ (1:ℝ[X]) 1
  simp only [anglePolynomialTest,eval_one,mul_one] at hi
  have hi' : Integrable (fun θ : ℝ => Real.sin θ^(4*Target.a κ))
      (volume.restrict (Ioo (0:ℝ) Real.pi)) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le] at hi
    exact hi.mono_set Ioo_subset_Ioc_self
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [angleEigenSquareNorm,angleEigenPolynomial_zero,anglePolynomialInner_eq_setIntegral]
  simp only [anglePolynomialTest,eval_one,mul_one]
  exact (ofReal_integral_eq_lintegral_ofReal hi' (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le _)).symm

lemma angleLaw_integral (κ : ℝ) (hκ : 0<κ) (f : ℝ → ℝ) :
    (∫ θ, f θ ∂Target.angleLaw κ)=
      (angleEigenSquareNorm κ 0)⁻¹*∫ θ in Ioo (0:ℝ) Real.pi,
        Real.sin θ^(4*Target.a κ)*f θ := by
  rw [Target.angleLaw,integral_smul_measure,ENNReal.toReal_inv,
    angle_normalizer_eq_norm hκ,ENNReal.toReal_ofReal (angleEigenSquareNorm_zero_pos hκ).le]
  congr 1
  have hm : Measurable (fun θ : ℝ => ENNReal.ofReal (Real.sin θ^(4*Target.a κ))) := by
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul
    hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le _)]
  rfl

lemma angleLaw_polynomial_pairing {κ : ℝ} (hκ : 0<κ) (p q : ℝ[X]) :
    (∫ θ, anglePolynomialTest p θ*anglePolynomialTest q θ ∂Target.angleLaw κ)=
      (angleEigenSquareNorm κ 0)⁻¹*anglePolynomialInner κ p q := by
  rw [angleLaw_integral κ hκ,anglePolynomialInner_eq_setIntegral]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ => by ring)

lemma angleLaw_eigen_orthogonal {κ : ℝ} (hκ : 0<κ) (n m : ℕ) (hnm : n≠m) :
    (∫ θ, anglePolynomialTest (angleEigenPolynomial κ n) θ*
      anglePolynomialTest (angleEigenPolynomial κ m) θ ∂Target.angleLaw κ)=0 := by
  rw [angleLaw_polynomial_pairing hκ]
  rw [show anglePolynomialInner κ (angleEigenPolynomial κ n) (angleEigenPolynomial κ m)=0
    from angleEigenPolynomial_orthogonal hκ n m hnm,mul_zero]

end SLEExactGauge

end

end OAI
