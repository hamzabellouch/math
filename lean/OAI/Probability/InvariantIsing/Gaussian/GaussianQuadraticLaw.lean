import OAI.Probability.InvariantIsing.Gaussian.GaussianQuadraticPotential
import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace OAI

/-! Identification of the normalized quadratic-potential law with stdGaussian. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma gaussianQuadratic_integral_cexp {d : ℕ} (t : EuclideanSpace ℝ (Fin d)) :
    (∫ x : EuclideanSpace ℝ (Fin d), Complex.exp
      (-(gaussianQuadraticPotential x : ℂ)+Complex.I*(inner ℝ t x)))=
    (LeanBlast.KLS.potentialPartition (gaussianQuadraticPotential (d := d)) : ℂ)*
      Complex.exp (-(‖t‖ : ℂ)^2/2) := by
  have hb := GaussianFourier.integral_cexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin d)) (b := (1/2 : ℂ)) (by norm_num)
  have hbase : (LeanBlast.KLS.potentialPartition (gaussianQuadraticPotential (d := d)) : ℂ)=
      (Real.pi/(1/2 : ℂ))^(Module.finrank ℝ (EuclideanSpace ℝ (Fin d))/2 : ℂ) := by
    rw [LeanBlast.KLS.potentialPartition,← integral_complex_ofReal]
    convert hb using 1
    congr 1
    funext x
    rw [Complex.ofReal_exp]
    congr 1
    simp [gaussianQuadraticPotential,Complex.ofReal_mul,Complex.ofReal_pow]
  have hf := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin d)) (b := (1/2 : ℂ)) (by norm_num) Complex.I t
  have he : Complex.I^2*(‖t‖ : ℂ)^2/(4*(1/2 : ℂ))=-(‖t‖ : ℂ)^2/2 := by
    rw [Complex.I_sq]
    ring
  rw [he,← hbase] at hf
  convert hf using 1
  congr 1
  funext x
  congr 1
  simp [gaussianQuadraticPotential,Complex.ofReal_mul,Complex.ofReal_pow]

lemma gaussianQuadratic_charFun {d : ℕ} (t : EuclideanSpace ℝ (Fin d)) :
    charFun (LeanBlast.KLS.potentialMeasure (gaussianQuadraticPotential (d := d))) t=
      Complex.exp (-(‖t‖ : ℂ)^2/2) := by
  let p := LeanBlast.KLS.potentialPartition (gaussianQuadraticPotential (d := d))
  have hp : (p : ℂ) ≠ 0 := by
    exact_mod_cast (LeanBlast.KLS.potentialPartition_pos (gaussianQuadraticPotential_integrable d)).ne'
  rw [charFun_apply,LeanBlast.KLS.potentialMeasure,integral_tilted]
  change (∫ x : EuclideanSpace ℝ (Fin d), (Real.exp (-gaussianQuadraticPotential x)/p) •
    Complex.exp ((inner ℝ x t : ℂ)*Complex.I))=_
  calc
    _ = (p : ℂ)⁻¹*(∫ x : EuclideanSpace ℝ (Fin d), Complex.exp
        (-(gaussianQuadraticPotential x : ℂ)+Complex.I*(inner ℝ t x))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_exp,Complex.exp_add]
      rw [Complex.ofReal_neg]
      have he : (inner ℝ x t : ℂ)*Complex.I=Complex.I*(inner ℝ t x) := by
        rw [real_inner_comm x t]
        exact mul_comm _ _
      rw [he]
      ring
    _ = _ := by
      rw [gaussianQuadratic_integral_cexp,← mul_assoc,inv_mul_cancel₀ hp,one_mul]

lemma gaussianQuadratic_potentialMeasure_eq_stdGaussian (d : ℕ) :
    LeanBlast.KLS.potentialMeasure (gaussianQuadraticPotential (d := d))=
      stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  let : IsProbabilityMeasure (LeanBlast.KLS.potentialMeasure (gaussianQuadraticPotential (d := d))) :=
    LeanBlast.KLS.isProbabilityMeasure_potentialMeasure (gaussianQuadraticPotential_integrable d)
  apply Measure.ext_of_charFun
  ext t
  rw [gaussianQuadratic_charFun,charFun_stdGaussian]

end InvariantIsing

end

end OAI
