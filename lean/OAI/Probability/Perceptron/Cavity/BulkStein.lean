import Mathlib
import OAI.Probability.Perceptron.Variational.FieldDerivative
import OAI.Probability.Perceptron.Variational.IntegratedConvex
import OAI.Probability.Perceptron.Cavity.BulkCoupling
import OAI.Probability.Perceptron.Pressure.SphericalPatternDirection

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkOverlapPower_measurable (N r : ℕ) :
    Measurable (fun x : Fin 2→NormalizedSpin N => spinOverlap (x 1) (x 0)^r) := by
  exact (((measurable_pi_apply 1).subtype_val).inner ((measurable_pi_apply 0).subtype_val)).pow_const r

lemma bulkOverlapPower_bound (N r : ℕ) (x : Fin 2→NormalizedSpin N) :
    |spinOverlap (x 1) (x 0)^r|≤1 := by
  rw [abs_pow]
  exact (pow_le_pow_left₀ (abs_nonneg _) (spinOverlap_abs_le _ _) r).trans_eq (one_pow r)

lemma bulk_fixed_patterns_ibp_raw (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (a : Fin M→Fin (n+1)→ℝ) :
    (∫ g, tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g)
      (bulkY (n+1) p g) 1 ∂stdGaussian (BulkMark (n+1))) =
    ∫ g, tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g)
      (fun x => inner ℝ (bulkDirection (n+1) p x) (bulkFeature (n+1) v x)) 1 -
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) 2
        (fun x => inner ℝ (bulkDirection (n+1) p (x 1)) (bulkFeature (n+1) v (x 0)))
    ∂stdGaussian (BulkMark (n+1)) := by
  have hW : Measurable (normalizedPatternEnergy (n+1) M f a) :=
    ((normalizedPatternEnergy_continuous (n+1) M f).comp
      (continuous_const.prodMk continuous_id)).measurable
  exact euclideanGaussian_tiltMean_ibp (unitSphereLaw (n+1)) hW
    (bulkFeature_continuous (n+1) v).measurable (bulkDirection_continuous (n+1) p).measurable
    (normalizedPatternEnergy_bound (n+1) M f a)
    (fun x => le_of_eq (bulkFeature_norm_sq (n+1) v x))
    (fun x => by rw [bulkDirection_norm]; norm_num : ∀ x, ‖bulkDirection (n+1) p x‖^2≤(1:ℝ))

lemma bulk_fixed_integrand_eq (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (a : Fin M→Fin (n+1)→ℝ) (g : BulkMark (n+1)) :
    tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g)
      (fun x => inner ℝ (bulkDirection (n+1) p x) (bulkFeature (n+1) v x)) 1 -
      gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) 2
        (fun x => inner ℝ (bulkDirection (n+1) p (x 1)) (bulkFeature (n+1) v (x 0))) =
    bulkAmplitude (n+1) v p*(1-gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a g) 2 (fun x => spinOverlap (x 1) (x 0)^(p.val+1))) := by
  have h1 : (fun x : NormalizedSpin (n+1) => inner ℝ (bulkDirection (n+1) p x) (bulkFeature (n+1) v x))=
      (fun _ => bulkAmplitude (n+1) v p) := by
    funext x
    rw [bulkFeature_direction_inner,spinOverlap_self,one_pow,mul_one]
  have h2 : (fun x : Fin 2→NormalizedSpin (n+1) => inner ℝ (bulkDirection (n+1) p (x 1)) (bulkFeature (n+1) v (x 0)))=
      (fun x => bulkAmplitude (n+1) v p*spinOverlap (x 1) (x 0)^(p.val+1)) := by
    funext x
    exact bulkFeature_direction_inner _ _ _ _ _
  have hp : 0<tiltPartition (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) 1 :=
    tilt_partition_pos_of_integrable _ (by simpa only [one_mul] using bulkHamiltonian_exp_integrable n M f v (a,g))
  rw [h1,h2,tiltMean_const_of_pos _ _ _ _ hp,gibbsReplicaMean,tiltMean_const_mul_general]
  change bulkAmplitude (n+1) v p - bulkAmplitude (n+1) v p * _ = bulkAmplitude (n+1) v p * (1-_)
  unfold gibbsReplicaMean
  ring

lemma bulk_replicaPower_integrable_fixed (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ)
    (a : Fin M→Fin (n+1)→ℝ) :
    Integrable (fun g => gibbsReplicaMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) 2
      (fun x => spinOverlap (x 1) (x 0)^r)) (stdGaussian (BulkMark (n+1))) := by
  exact kernel_replicaMean_bounded_integrable (Kernel.const (BulkMark (n+1)) (unitSphereLaw (n+1)))
    (stdGaussian (BulkMark (n+1)))
    (H := fun g x => bulkHamiltonian (n+1) M f v a g x)
    (G := fun _ x => spinOverlap (x 1) (x 0)^r)
    (((bulkHamiltonian_continuous (n+1) M f v).comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)).measurable)
    ((bulkOverlapPower_measurable (n+1) r).comp measurable_snd)
    zero_le_one (fun _ x => bulkOverlapPower_bound _ _ x)

lemma bulk_fixed_patterns_ibp (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (a : Fin M→Fin (n+1)→ℝ) :
    (∫ g, tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g)
      (bulkY (n+1) p g) 1 ∂stdGaussian (BulkMark (n+1))) =
    bulkAmplitude (n+1) v p*(1-∫ g, gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a g) 2
      (fun x => spinOverlap (x 1) (x 0)^(p.val+1)) ∂stdGaussian (BulkMark (n+1))) := by
  rw [bulk_fixed_patterns_ibp_raw]
  simp_rw [bulk_fixed_integrand_eq]
  rw [integral_const_mul,integral_sub (integrable_const _) (bulk_replicaPower_integrable_fixed n M f v (p.val+1) a)]
  simp

lemma bulk_meanY_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    Measurable (fun a : BulkDisorder (n+1) M => tiltMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) (bulkY (n+1) p a.2) 1) :=
  kernel_tiltMean_measurable (bulkSpinKernel n M)
    (H := fun a x => bulkHamiltonian (n+1) M f v a.1 a.2 x)
    (Y := fun a x => bulkY (n+1) p a.2 x)
    (bulkHamiltonian_continuous _ _ _ _).measurable (bulkY_joint_measurable _ _ _)

lemma bulk_meanY_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1))
    (a : BulkDisorder (n+1) M) :
    |tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2)
      (bulkY (n+1) p a.2) 1|≤‖a.2‖ := by
  exact tiltMean_bound_of_integrable _ (bulkHamiltonian_section_measurable _ _ _ _ a)
    (bulkY_measurable _ _).of_uncurry_left
    (by simpa only [one_mul] using bulkHamiltonian_exp_integrable n M f v a)
    (bulkY_bound _ _ _)

lemma bulk_meanY_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    Integrable (fun a : BulkDisorder (n+1) M => tiltMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) (bulkY (n+1) p a.2) 1) (bulkDisorderLaw (n+1) M) := by
  have hi : Integrable (fun g : BulkMark (n+1) => ‖g‖) (stdGaussian (BulkMark (n+1))) :=
    ((IsGaussian.memLp_id (stdGaussian (BulkMark (n+1))) 2 (by simp)).norm).integrable (by norm_num)
  apply (hi.comp_snd (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)))).mono'
    (bulk_meanY_measurable n M f v p).aestronglyMeasurable
  exact ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using bulk_meanY_bound n M f v p a

lemma bulk_replicaPower_integrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (r : ℕ) :
    Integrable (fun a : BulkDisorder (n+1) M => gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) 2 (fun x => spinOverlap (x 1) (x 0)^r))
      (bulkDisorderLaw (n+1) M) :=
  kernel_replicaMean_bounded_integrable (bulkSpinKernel n M) _
    (H := fun a x => bulkHamiltonian (n+1) M f v a.1 a.2 x)
    (G := fun _ x => spinOverlap (x 1) (x 0)^r)
    (bulkHamiltonian_continuous _ _ _ _).measurable
    ((bulkOverlapPower_measurable _ _).comp measurable_snd) zero_le_one
    (fun _ x => bulkOverlapPower_bound _ _ x)

lemma bulk_annealed_ibp (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    (∫ a, tiltMean (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a.1 a.2)
      (bulkY (n+1) p a.2) 1 ∂bulkDisorderLaw (n+1) M) =
    bulkAmplitude (n+1) v p*(1-∫ a, gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) 2
      (fun x => spinOverlap (x 1) (x 0)^(p.val+1)) ∂bulkDisorderLaw (n+1) M) := by
  rw [bulkDisorderLaw,integral_prod _ (bulk_meanY_integrable n M f v p)]
  simp_rw [bulk_fixed_patterns_ibp]
  rw [integral_const_mul,integral_sub (integrable_const _)
    (bulk_replicaPower_integrable n M f v (p.val+1)).integral_prod_left]
  rw [integral_const]
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  rw [← integral_prod _ (bulk_replicaPower_integrable n M f v (p.val+1))]

lemma bulk_expected_slope_eq (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (u : ℝ) :
    (∫ a, bulkCouplingSlope n M f v p u a ∂bulkDisorderLaw (n+1) M) =
    bulkCoefficient (n+1) p^2*u*(1-∫ a, gibbsReplicaMean (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f (Function.update v (p.val+1) u) a.1 a.2) 2
      (fun x => spinOverlap (x 1) (x 0)^(p.val+1)) ∂bulkDisorderLaw (n+1) M) := by
  unfold bulkCouplingSlope
  rw [integral_const_mul,bulk_annealed_ibp]
  simp only [bulkAmplitude,Function.update_self,bulkCoefficient]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
