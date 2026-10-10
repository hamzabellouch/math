import Mathlib
import OAI.Probability.Perceptron.Interpolation.CountableGaussianReplicaIBP
import OAI.Probability.Perceptron.Variational.GaussianEnergyMoments

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
variable {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
variable (hL : Measurable L) {A D E : ℝ} (hA : ∀ x, |W x| ≤ A)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)
omit [MeasurableSpace S] in
lemma gaussianTailCoefficient_zero (w : ℕ → S → ℝ) : gaussianTailCoefficient w 0=w := by
  funext i x
  simp [gaussianTailCoefficient]

include hW hv hw hL hA hD hE

lemma gaussianEnergy_tail_tilt_integrable (n : ℕ) :
    Integrable (fun g => tiltMean μ (countableGaussianHamiltonian W v L g)
      (fun x => |countableGaussianField (gaussianTailCoefficient w n) L g x|) 1) countableGaussianLaw := by
  apply tiltMean_abs_annealed_integrable μ countableGaussianLaw
    (countableGaussianHamiltonian_measurable hW hv hL)
    (countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL)
    (gaussianHamiltonianPartition_inverse_power_integrable μ hW hv hL hA hD 2)
  simpa only [sq_abs] using gaussianEnergy_weighted_moment_joint_integrable hW hv hw hL hA hD hE μ n 2 2

lemma gaussianEnergy_tail_tilt_tendsto :
    Tendsto (fun n => ∫ g, tiltMean μ (countableGaussianHamiltonian W v L g)
      (fun x => |countableGaussianField (gaussianTailCoefficient w n) L g x|) 1 ∂countableGaussianLaw)
      atTop (nhds 0) := by
  have hlim := (gaussianEnergy_tail_weighted_L2 hW hv hw hL hA hD hE μ 2).sqrt.const_mul
    (Real.sqrt (∫ g, (tiltPartition μ (countableGaussianHamiltonian W v L g) 1)⁻¹^2 ∂countableGaussianLaw))
  simp only [Real.sqrt_zero,mul_zero] at hlim
  apply squeeze_zero (fun n => integral_nonneg fun g => ?_) (fun n => ?_) hlim
  · unfold tiltMean tiltIntegral tiltPartition
    exact div_nonneg (integral_nonneg (fun _ => by positivity)) (integral_nonneg (fun _ => by positivity))
  · have h := tiltMean_abs_annealed_L2_bound μ countableGaussianLaw
      (countableGaussianHamiltonian_measurable hW hv hL)
      (countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL)
      (gaussianHamiltonianPartition_inverse_power_integrable μ hW hv hL hA hD 2)
      (by simpa only [sq_abs] using gaussianEnergy_weighted_moment_joint_integrable hW hv hw hL hA hD hE μ n 2 2)
    simpa only [countableGaussianField_tail] using h

lemma gaussianEnergy_tail_weighted_integrable_ae (n : ℕ) :
    ∀ᵐ g ∂countableGaussianLaw,
      Integrable (fun x => Real.exp (countableGaussianHamiltonian W v L g x)*
        countableGaussianField (gaussianTailCoefficient w n) L g x) μ := by
  filter_upwards [(gaussianEnergy_weighted_moment_joint_integrable hW hv hw hL hA hD hE μ n 1 1).prod_left_ae] with g hg
  apply hg.mono'
  · exact (((countableGaussianHamiltonian_measurable hW hv hL).comp
      (measurable_const.prodMk measurable_id)).exp.mul
      ((countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · exact ae_of_all _ fun x => by simp only [Real.norm_eq_abs,abs_mul,Real.abs_exp,pow_one,one_mul]; exact le_of_eq (mul_comm _ _)

lemma gaussianEnergy_tail_replica_integrable {r : ℕ} (j : Fin r) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) (n : ℕ) :
    Integrable (fun g => gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
      (fun x => countableGaussianField (gaussianTailCoefficient w n) L g (x j)*G x)) countableGaussianLaw := by
  have hm : Measurable (fun p : (ℕ → ℝ)×(Fin r → S) =>
      countableGaussianField (gaussianTailCoefficient w n) L p.1 (p.2 j)*G p.2) :=
    ((countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL).comp
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))).mul (hG.comp measurable_snd)
  apply ((gaussianEnergy_tail_tilt_integrable μ hW hv hw hL hA hD hE n).const_mul B).mono'
    (replicaMean_varying_measurable μ (countableGaussianHamiltonian_measurable hW hv hL) hm).aestronglyMeasurable
  filter_upwards [(countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae,
    gaussianEnergy_tail_weighted_integrable_ae μ hW hv hw hL hA hD hE n] with g hg hf
  simpa only [Real.norm_eq_abs] using replicaMean_energy_bound μ j (H := countableGaussianHamiltonian W v L g)
    (F := countableGaussianField (gaussianTailCoefficient w n) L g)
    ((countableGaussianHamiltonian_measurable hW hv hL).comp (measurable_const.prodMk measurable_id))
    ((countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL).comp
      (measurable_const.prodMk measurable_id)) hG (by simpa only [one_mul] using hg) hf hB hGB

lemma gaussianEnergy_tail_replica_tendsto {r : ℕ} (j : Fin r) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Tendsto (fun n => ∫ g, gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
      (fun x => countableGaussianField (gaussianTailCoefficient w n) L g (x j)*G x) ∂countableGaussianLaw)
      atTop (nhds 0) := by
  have ht := (gaussianEnergy_tail_tilt_tendsto μ hW hv hw hL hA hD hE).const_mul B
  simp only [mul_zero] at ht
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _) (fun n => ?_) ht
  calc
    _ ≤ ∫ g, |gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
        (fun x => countableGaussianField (gaussianTailCoefficient w n) L g (x j)*G x)| ∂countableGaussianLaw := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := countableGaussianLaw)
        (fun g => gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
          (fun x => countableGaussianField (gaussianTailCoefficient w n) L g (x j)*G x))
    _ ≤ B*(∫ g, tiltMean μ (countableGaussianHamiltonian W v L g)
        (fun x => |countableGaussianField (gaussianTailCoefficient w n) L g x|) 1 ∂countableGaussianLaw) := by
      rw [← integral_const_mul]
      apply integral_mono_ae (gaussianEnergy_tail_replica_integrable μ hW hv hw hL hA hD hE j hG hB hGB n).abs
        ((gaussianEnergy_tail_tilt_integrable μ hW hv hw hL hA hD hE n).const_mul B)
      filter_upwards [(countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae,
        gaussianEnergy_tail_weighted_integrable_ae μ hW hv hw hL hA hD hE n] with g hg hf
      exact replicaMean_energy_bound μ j (H := countableGaussianHamiltonian W v L g)
        (F := countableGaussianField (gaussianTailCoefficient w n) L g)
        ((countableGaussianHamiltonian_measurable hW hv hL).comp (measurable_const.prodMk measurable_id))
        ((countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL).comp
          (measurable_const.prodMk measurable_id)) hG (by simpa only [one_mul] using hg) hf hB hGB

lemma gaussianEnergy_replica_integrable {r : ℕ} (j : Fin r) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Integrable (fun g => gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
      (fun x => countableGaussianField w L g (x j)*G x)) countableGaussianLaw := by
  simpa only [gaussianTailCoefficient_zero] using
    gaussianEnergy_tail_replica_integrable μ hW hv hw hL hA hD hE j hG hB hGB 0

lemma gaussianEnergy_replica_prefix_tendsto {r : ℕ} (j : Fin r) {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Tendsto (fun n => ∫ g, gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
      (fun x => truncatedCountableGaussianField w L n g (x j)*G x) ∂countableGaussianLaw) atTop
      (nhds (∫ g, gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
        (fun x => countableGaussianField w L g (x j)*G x) ∂countableGaussianLaw)) := by
  have hc : Tendsto (fun _ : ℕ => ∫ g, gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
      (fun x => countableGaussianField w L g (x j)*G x) ∂countableGaussianLaw) atTop
      (nhds (∫ g, gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) r
        (fun x => countableGaussianField w L g (x j)*G x) ∂countableGaussianLaw)) := tendsto_const_nhds
  have ht := hc.sub (gaussianEnergy_tail_replica_tendsto μ hW hv hw hL hA hD hE j hG hB hGB)
  simp only [sub_zero] at ht
  apply ht.congr
  intro n
  rw [← integral_sub (gaussianEnergy_replica_integrable μ hW hv hw hL hA hD hE j hG hB hGB)
    (gaussianEnergy_tail_replica_integrable μ hW hv hw hL hA hD hE j hG hB hGB n)]
  apply integral_congr_ae
  have hf := gaussianEnergy_tail_weighted_integrable_ae μ hW hv hw hL hA hD hE 0
  simp only [gaussianTailCoefficient_zero] at hf
  filter_upwards [(countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae,
    hf,gaussianEnergy_tail_weighted_integrable_ae μ hW hv hw hL hA hD hE n] with g hg hfg hqg
  have hh : Measurable (countableGaussianHamiltonian W v L g) :=
    (countableGaussianHamiltonian_measurable hW hv hL).comp (measurable_const.prodMk measurable_id)
  have hff : Measurable (countableGaussianField w L g) :=
    (countableGaussianField_measurable hw hL).comp (measurable_const.prodMk measurable_id)
  have hq : Measurable (countableGaussianField (gaussianTailCoefficient w n) L g) :=
    (countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL).comp
      (measurable_const.prodMk measurable_id)
  have heq := replicaMean_energy_sub μ j hh hff hq hG (by simpa only [one_mul] using hg) hfg hqg hGB
  simpa only [countableGaussianField_tail,sub_sub_cancel] using heq.symm

end SphericalPerceptronFreeEnergy
end

end OAI
