import Mathlib
import OAI.Probability.LogConcave.Model
import OAI.Probability.LogConcave.Sampling.LintegralFinNatProd

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling

theorem map_withDensity_of_measurePreserving {E F : Type*}
    [MeasurableSpace E] [MeasurableSpace F] {μ : Measure E} {ν : Measure F}
    (e : E ≃ᵐ F) (he : MeasurePreserving e μ ν) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = ν.withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs]
  have h := he.setLIntegral_comp_preimage hs (hf.comp e.symm.measurable)
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using h

end LogConcaveSampling

namespace LogConcaveSampling
namespace EulerDensity
open ProbabilityTheory MeasureTheory WithLp
open scoped ENNReal NNReal RealInnerProductSpace

def gaussianCoefficient (d : ℕ) : ℝ≥0∞ :=
  ∏ _ : Fin d, ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹)

lemma standard_pi_density (d : ℕ) :
    Measure.pi (fun _ : Fin d => gaussianReal 0 1) =
      (volume : Measure (Fin d → ℝ)).withDensity
        (fun x => gaussianCoefficient d*ENNReal.ofReal (Real.exp (-(∑ k, (x k)^2)/2))) := by
  have hg : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero _ (by norm_num)
  have : IsProbabilityMeasure (volume.withDensity (gaussianPDF 0 1)) := by rw [← hg]; infer_instance
  simp_rw [hg]
  rw [pi_withDensity_fin _ _ (fun _ => measurable_gaussianPDF _ _)]
  congr 1
  ext x
  have he (z : ℝ) : gaussianPDF 0 1 z =
      ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹)*ENNReal.ofReal (Real.exp (-z^2/2)) := by
    simp [gaussianPDF,gaussianPDFReal]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div,Finset.sum_neg_distrib]

theorem standard_density (d : ℕ) :
    stdGaussian (Point d) = gaussianCoefficient d •
      (volume : Measure (Point d)).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-‖z‖^2/2))) := by
  rw [← map_pi_eq_stdGaussian,standard_pi_density]
  let e : (Fin d → ℝ) ≃ᵐ Point d := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  change Measure.map e _ = _
  rw [map_withDensity_of_measurePreserving e (PiLp.volume_preserving_toLp (Fin d)) (by fun_prop)]
  have he : (fun y : Point d => gaussianCoefficient d*
      ENNReal.ofReal (Real.exp (-(∑ k, (e.symm y k)^2)/2))) =
      gaussianCoefficient d • (fun z : Point d => ENNReal.ofReal (Real.exp (-‖z‖^2/2))) := by
    funext y
    simp only [Pi.smul_apply,smul_eq_mul]
    congr 3
    change -(∑ k, (y k)^2)/2 = -‖y‖^2/2
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs,sq_abs]
  rw [he,withDensity_smul]
  fun_prop

lemma gaussianCoefficient_positive (d : ℕ) : 0 < gaussianCoefficient d := by
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)

lemma gaussianCoefficient_finite (d : ℕ) : gaussianCoefficient d ≠ ⊤ := by
  exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)

lemma standard_partition (d : ℕ) :
    (gaussianCoefficient d).toReal*(∫ z : Point d, Real.exp (-‖z‖^2/2)) = 1 := by
  have he := congrArg (fun μ : Measure (Point d) => μ Set.univ) (standard_density d)
  rw [measure_univ,Measure.smul_apply,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,smul_eq_mul] at he
  have hh := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_one,ENNReal.toReal_mul] at hh
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
    (by fun_prop)]
  exact hh.symm

def shear {d : ℕ} (T : Point d → Point d) (hT : Measurable T) :
    Point d × Point d ≃ᵐ Point d × Point d where
  toFun p := (p.1,T p.1+p.2)
  invFun p := (p.1,p.2-T p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  measurable_toFun := measurable_fst.prodMk ((hT.comp measurable_fst).add measurable_snd)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.sub (hT.comp measurable_fst))

lemma shear_measurePreserving {d : ℕ} {T : Point d → Point d} (hT : Measurable T) :
    MeasurePreserving (shear T hT) ((volume : Measure (Point d)).prod volume)
      ((volume : Measure (Point d)).prod volume) := by
  exact (MeasurePreserving.id volume).skew_product ((hT.comp measurable_fst).add measurable_snd)
    (Filter.Eventually.of_forall (fun x => map_add_left_eq_self volume (T x)))

end EulerDensity
end LogConcaveSampling

namespace LogConcaveSampling
namespace EulerDensity
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

lemma map_withDensity_equiv {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (e : E ≃ᵐ F) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) :=
  map_withDensity_of_measurePreserving e ⟨e.measurable,rfl⟩ hf

def noiseCoefficient (d : ℕ) (σ : ℝ) : ℝ≥0∞ :=
  gaussianCoefficient d*ENNReal.ofReal |(σ^d)⁻¹|

lemma scaled_standard_density (d : ℕ) {σ : ℝ} (hσ : σ ≠ 0) :
    (stdGaussian (Point d)).map (fun z => σ • z) =
      noiseCoefficient d σ • (volume : Measure (Point d)).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-‖z‖^2/(2*σ^2)))) := by
  let e := (Homeomorph.smulOfNeZero (α := Point d) σ hσ).toMeasurableEquiv
  rw [standard_density,Measure.map_smul _ (by fun_prop)]
  change gaussianCoefficient d • (Measure.map e _) = _
  rw [map_withDensity_equiv volume e (by fun_prop)]
  have he : (volume : Measure (Point d)).map e =
      ENNReal.ofReal |(σ^d)⁻¹| • volume := by
    convert! Measure.map_addHaar_smul (volume : Measure (Point d)) hσ using 1
    simp [Point]
  rw [he,withDensity_smul_measure,smul_smul]
  congr 2
  funext z
  have hz : e.symm z = σ⁻¹ • z := by
    exact congrFun (Homeomorph.smulOfNeZero_symm_apply hσ) z
  rw [hz,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  congr 2
  field_simp

lemma noiseCoefficient_positive (d : ℕ) {σ : ℝ} (hσ : σ ≠ 0) :
    0 < noiseCoefficient d σ := by
  apply ENNReal.mul_pos_iff.mpr
  exact ⟨gaussianCoefficient_positive d,ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hσ)))⟩

lemma noiseCoefficient_finite (d : ℕ) (σ : ℝ) : noiseCoefficient d σ ≠ ⊤ :=
  ENNReal.mul_ne_top (gaussianCoefficient_finite d) ENNReal.ofReal_ne_top

theorem joint_density {d : ℕ} {H : Point d → ℝ} (hH : Measurable H)
    (T : Point d → Point d) (hT : Measurable T) {σ : ℝ} (hσ : σ ≠ 0) :
    ((gibbs H).prod (stdGaussian (Point d))).map (fun p => (p.1,T p.1+σ • p.2)) =
      ((partition H)⁻¹*noiseCoefficient d σ) •
        ((volume : Measure (Point d)).prod volume).withDensity
          (fun p => ENNReal.ofReal (Real.exp (-H p.1-‖p.2-T p.1‖^2/(2*σ^2)))) := by
  have : SFinite (gibbs H) := by unfold gibbs; infer_instance
  have hmap : ((gibbs H).prod (stdGaussian (Point d))).map
      (fun p => (p.1,T p.1+σ • p.2)) =
      (((gibbs H).prod ((stdGaussian (Point d)).map (fun z => σ • z))).map (shear T hT)) := by
    have hj := Measure.map_prod_map (gibbs H) (stdGaussian (Point d)) measurable_id
      (show Measurable (fun z : Point d => σ • z) by fun_prop)
    simp only [Measure.map_id] at hj
    rw [hj,Measure.map_map (shear T hT).measurable (by fun_prop)]
    rfl
  rw [hmap,scaled_standard_density d hσ]
  unfold gibbs
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,
    prod_withDensity (by unfold gibbsDensity; fun_prop) (by fun_prop),
    Measure.map_smul _ (shear T hT).measurable.aemeasurable,
    map_withDensity_of_measurePreserving (shear T hT) (shear_measurePreserving hT) (by unfold gibbsDensity; fun_prop)]
  congr 2
  funext p
  change ENNReal.ofReal (Real.exp (-H p.1))*
    ENNReal.ofReal (Real.exp (-‖p.2-T p.1‖^2/(2*σ^2))) = _
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

end EulerDensity
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
