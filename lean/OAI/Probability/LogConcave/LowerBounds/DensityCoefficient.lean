import Mathlib
import OAI.Probability.LogConcave.Analysis.GaussianCoefficient
import OAI.Probability.LogConcave.LowerBounds.SpectrumOperator
import OAI.Probability.LogConcave.Analysis.GibbsProportional

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open Polynomial
open scoped BigOperators

namespace LogConcaveSampling.LowerBound
open Matrix WithLp ProbabilityTheory
open scoped RealInnerProductSpace

lemma targetVariance_ne_zero (d k : ℕ) : targetVariance d k ≠ 0 := by
  apply ne_of_gt
  change 0 < (eigenvalue d k)⁻¹
  apply inv_pos.mpr
  linarith [(eigenvalue_bounds d k).1]

def densityCoefficient (d : ℕ) : ℝ≥0∞ :=
  ∏ k : Fin d, ENNReal.ofReal ((Real.sqrt (2*Real.pi*(targetVariance d k : ℝ)))⁻¹)

lemma gaussianPDF_targetVariance (d k : ℕ) (x : ℝ) :
    gaussianPDF 0 (targetVariance d k) x =
      ENNReal.ofReal ((Real.sqrt (2*Real.pi*(targetVariance d k : ℝ)))⁻¹) *
        ENNReal.ofReal (Real.exp (-(eigenvalue d k * x^2) / 2)) := by
  unfold gaussianPDF gaussianPDFReal
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 2
  apply congrArg Real.exp
  change -(x - 0)^2 / (2 * (eigenvalue d k)⁻¹) = -(eigenvalue d k * x^2) / 2
  simp only [sub_zero, div_mul_eq_div_div, div_inv_eq_mul]
  ring

lemma targetGaussian_density (d : ℕ) :
    targetGaussian d = (volume : Measure (Fin d → ℝ)).withDensity
      (fun x => densityCoefficient d *
        ENNReal.ofReal (Real.exp (-(∑ k : Fin d, eigenvalue d k * (x k)^2) / 2))) := by
  have hg (k : Fin d) : gaussianReal 0 (targetVariance d k) =
      volume.withDensity (gaussianPDF 0 (targetVariance d k)) :=
    gaussianReal_of_var_ne_zero _ (targetVariance_ne_zero d k)
  have (k : Fin d) : IsProbabilityMeasure
      (volume.withDensity (gaussianPDF 0 (targetVariance d k))) := by
    rw [← hg k]
    infer_instance
  unfold targetGaussian
  simp_rw [hg]
  rw [pi_withDensity_fin _ _ (fun _ => measurable_gaussianPDF _ _)]
  congr 1
  ext x
  simp_rw [gaussianPDF_targetVariance]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

lemma quadraticPotential_eq_spectral {d : ℕ} (O : Rotations d) (x : Point d) :
    quadraticPotential O x =
      (∑ k : Fin d, eigenvalue d k * ((rotationIsometry O).symm x k)^2) / 2 := by
  unfold quadraticPotential
  congr 1
  change inner ℝ x ((rotationIsometry O)
    (spectrumOperator d ((rotationIsometry O).symm x))) = _
  rw [← (rotationIsometry O).apply_symm_apply x]
  simp only [LinearIsometryEquiv.inner_map_map, PiLp.inner_apply, Real.inner_apply,
      spectrumOperator_apply, LinearIsometryEquiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem quadratic_gibbs_eq_gaussian {d : ℕ} (O : Rotations d) :
    (targetGaussian d).map (fun u => rotationIsometry O (toLp 2 u)) =
      gibbs (quadraticPotential O) := by
  apply eq_gibbs_of_proportional (C := densityCoefficient d)
  let e : (Fin d → ℝ) ≃ᵐ Point d :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).trans (rotationIsometry O).toMeasurableEquiv
  have he : MeasurePreserving e volume volume :=
    (rotationIsometry O).measurePreserving.comp (PiLp.volume_preserving_toLp (Fin d))
  change (targetGaussian d).map e = _
  rw [targetGaussian_density, map_withDensity_of_measurePreserving e he (by fun_prop)]
  have hfun : (fun y : Point d => densityCoefficient d *
        ENNReal.ofReal (Real.exp (-(∑ k : Fin d, eigenvalue d k * (e.symm y k)^2)/2))) =
      densityCoefficient d • gibbsDensity (quadraticPotential O) := by
    ext y
    simp only [Pi.smul_apply, smul_eq_mul, gibbsDensity, quadraticPotential_eq_spectral]
    simp only [neg_div]
    rfl
  rw [hfun, withDensity_smul]
  exact (Real.continuous_exp.comp
    (quadraticPotential_admissible O).smooth.continuous.neg).measurable.ennreal_ofReal

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
