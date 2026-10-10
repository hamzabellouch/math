import Mathlib
import OAI.Probability.Perceptron.Interpolation.IntegrableReplicaGibbs

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tiltMean_restore {H W F : S→ℝ} (_hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) :
    tiltMean μ (fun x => H x+W x) F 1 =
      tiltMean μ H (fun x => Real.exp (W x)*F x) 1 /
        tiltMean μ H (fun x => Real.exp (W x)) 1 := by
  have hp : tiltPartition μ H 1≠0 :=
    (tilt_partition_pos_of_integrable μ (by simpa only [one_mul] using hi)).ne'
  simp only [tiltMean,tiltIntegral,tiltPartition,one_mul,Real.exp_add,mul_assoc]
  have hp' : (∫ x, Real.exp (H x) ∂μ) ≠ 0 := by
    simpa only [tiltPartition,one_mul] using hp
  exact (div_div_div_cancel_right₀ hp' _ _).symm

lemma gibbsReplicaMean_fintype_prod {H F : S→ℝ} (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (r : ℕ) :
    gibbsReplicaMean μ H r (fun x => ∏ i, F (x i))=(tiltMean μ H F 1)^r := by
  have hi' : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using hi
  let := tilt_law_probability_of_integrable μ hi'
  rw [gibbsReplicaMean_integral_of_integrable μ hH hi,
    ← tilt_law_integral_of_integrable μ hH hi']
  simpa only [Fintype.card_fin] using integral_fintype_prod_eq_pow (ι:=Fin r) F (μ:=tiltLaw μ H 1)

lemma gibbsReplicaMean_restore {H W : S→ℝ} (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H x)) μ) (r : ℕ) (F : (Fin r→S)→ℝ) :
    gibbsReplicaMean μ (fun x => H x+W x) r F =
      gibbsReplicaMean μ H r (fun x => (∏ i, Real.exp (W (x i)))*F x) /
        (tiltMean μ H (fun x => Real.exp (W x)) 1)^r := by
  have hp : replicaPotential (fun x => H x+W x) r =
      fun x => replicaPotential H r x+replicaPotential W r x := by
    funext x; simp only [replicaPotential,Finset.sum_add_distrib]
  have hir : Integrable (fun x => Real.exp (replicaPotential H r x)) (Measure.pi fun _ : Fin r => μ) := by
    simpa only [one_mul] using (replica_exp_integrable μ
      (show Integrable (fun x => Real.exp (1*H x)) μ by simpa only [one_mul] using hi) r)
  unfold gibbsReplicaMean
  rw [hp,tiltMean_restore _ (replicaPotential_measurable hH r) hir]
  simp only [replicaPotential,Real.exp_sum]
  congr 1
  exact gibbsReplicaMean_fintype_prod μ (F:=fun x => Real.exp (W x)) hH hi r

lemma tiltMean_exp_bounds {H W : S→ℝ} (hH : Measurable H) (hW : Measurable W)
    (hi : Integrable (fun x => Real.exp (H x)) μ) {C : ℝ} (_hC : 0≤C)
    (hWb : ∀ x, |W x|≤C) :
    Real.exp (-C) ≤ tiltMean μ H (fun x => Real.exp (W x)) 1 ∧
      tiltMean μ H (fun x => Real.exp (W x)) 1 ≤ Real.exp C := by
  have hi' : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using hi
  let := tilt_law_probability_of_integrable μ hi'
  rw [←tilt_law_integral_of_integrable μ hH hi']
  have hI : Integrable (fun x => Real.exp (W x)) (tiltLaw μ H 1) := by
    apply Integrable.of_bound hW.exp.aestronglyMeasurable (Real.exp C)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (abs_le.mp (hWb x)).2
  constructor
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono (integrable_const (Real.exp (-C))) hI
        (fun x => Real.exp_le_exp.mpr (abs_le.mp (hWb x)).1)
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono hI (integrable_const (Real.exp C))
        (fun x => Real.exp_le_exp.mpr (abs_le.mp (hWb x)).2)
end SphericalPerceptronFreeEnergy
end

end OAI
