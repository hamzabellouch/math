import Mathlib
import OAI.Probability.Perceptron.Variational.CountableGaussianFullIBP
import OAI.Probability.Perceptron.Variational.UnboundedContact

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma abs_log_le_self_add_inv {x : ℝ} (hx : 0<x) : |Real.log x|≤x+x⁻¹ := by
  apply abs_le.mpr
  constructor
  · have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    rw [Real.log_inv] at hh
    linarith
  · exact (Real.log_le_sub_one_of_pos hx).trans (by linarith [inv_nonneg.mpr hx.le])

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
variable {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
variable (hL : Measurable L) {A D E : ℝ} (hA : ∀ x, |W x|≤A)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2)≤D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2)≤E)

include hW hv hL hA hD in
lemma gaussianLogPartition_integrable :
    Integrable (fun g => Real.log (tiltPartition μ (countableGaussianHamiltonian W v L g) 1)) countableGaussianLaw := by
  have hi : Integrable (fun g => tiltPartition μ (countableGaussianHamiltonian W v L g) 1) countableGaussianLaw := by
    simpa only [tiltPartition,one_mul] using
      (countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).integral_prod_right
  have hj : Integrable (fun g => (tiltPartition μ (countableGaussianHamiltonian W v L g) 1)⁻¹) countableGaussianLaw := by
    simpa only [pow_one] using gaussianHamiltonianPartition_inverse_power_integrable μ hW hv hL hA hD 1
  refine (hi.add hj).mono' ((gaussianHamiltonianPartition_measurable μ hW hv hL).log.aestronglyMeasurable) ?_
  filter_upwards [gaussianHamiltonianPartition_pos_ae μ hW hv hL hA hD] with g hg
  simpa only [Real.norm_eq_abs,Pi.add_apply] using abs_log_le_self_add_inv hg

include hW hv hw hL hA hD hE

lemma gaussianCouplingLog_integrable (a : ℝ) :
    Integrable (fun g => Real.log (tiltPartition μ (fun x =>
      countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 1)) countableGaussianLaw := by
  have hm (i : ℕ) : Measurable (fun x => v i x+a*w i x) := (hv i).add ((hw i).const_mul a)
  have hb (x : S) : (∑ i : Fin (L x), (v i.val x+a*w i.val x)^2)≤2*D+2*a^2*E := by
    simpa only [gaussianTailCoefficient,zero_le,ite_true,one_mul,mul_one,one_pow] using
      gaussianCombinedCoefficient_sq_bound v w L hD hE 1 a 0 x
  convert gaussianLogPartition_integrable μ hW hm hL hA hb using 1
  ext g
  congr 3
  ext x
  simp only [countableGaussianHamiltonian,countableGaussianField_add,countableGaussianField_smul]
  ring

lemma gaussianCouplingMean_derivative (a : ℝ) :
    HasDerivAt (fun b => ∫ g, Real.log (tiltPartition μ (fun x =>
      countableGaussianHamiltonian W v L g x+b*countableGaussianField w L g x) 1) ∂countableGaussianLaw)
      (∫ g, tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
        (countableGaussianField w L g) 1 ∂countableGaussianLaw) a := by
  let H := countableGaussianHamiltonian W v L
  let Y := countableGaussianField w L
  have hH : Measurable (Function.uncurry H) := countableGaussianHamiltonian_measurable hW hv hL
  have hY : Measurable (Function.uncurry Y) := countableGaussianField_measurable hw hL
  have hi := gaussianCouplingLog_integrable μ hW hv hw hL hA hD hE
  apply (annealed_convex_hasDerivAt countableGaussianLaw (fun b => (hi b).aestronglyMeasurable) _ hi _ a).2
  · intro b
    exact (kernel_tiltMean_measurable (Kernel.const _ μ) (hH.add (hY.const_mul b)) hY).aestronglyMeasurable
  · filter_upwards [countableGaussian_all_coupling_exp_ae μ hW hv hw hL hA hD hE] with g hg
    have hHg : Measurable (H g) := hH.of_uncurry_left
    have hYg : Measurable (Y g) := hY.of_uncurry_left
    exact ⟨coupling_log_convex μ hHg hYg hg,fun b => coupling_log_hasDerivAt μ hHg hYg hg b⟩

lemma annealedGaussianTiltMean_ibp :
    (∫ g, tiltMean μ (countableGaussianHamiltonian W v L g)
      (countableGaussianField w L g) 1 ∂countableGaussianLaw) =
    ∫ g, tiltMean μ (countableGaussianHamiltonian W v L g)
        (fun x => countableGaussianCovariance v w L x x) 1 -
      gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) 2
        (fun x => countableGaussianCovariance v w L (x 1) (x 0)) ∂countableGaussianLaw := by
  have hH := countableGaussianHamiltonian_measurable hW hv hL
  have hY := countableGaussianField_measurable hw hL
  have hK := countableGaussianCovariance_measurable hv hw hL
  have he : ∀ᵐ g ∂countableGaussianLaw, Integrable
      (fun x => Real.exp (countableGaussianHamiltonian W v L g x)) μ := by
    simpa only [one_mul] using
      (countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae
  have hb := countableGaussian_replica_full_ibp μ 1 (0 : Fin 1) hW hv hw hL
    (G := fun _ => 1) measurable_const hA hD hE (B := 1) (by norm_num) (by simp)
  simp only [mul_one,one_mul,Fin.sum_univ_one,Nat.cast_one] at hb
  calc
    _ = ∫ g, gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) 1
      (fun x => countableGaussianField w L g (x 0)) ∂countableGaussianLaw := by
      apply integral_congr_ae
      filter_upwards [he] with g hg
      exact (gibbsReplicaMean_coordinate_of_integrable μ hH.of_uncurry_left hY.of_uncurry_left hg 1 0).symm
    _ = _ := hb.trans (integral_congr_ae (by
      filter_upwards [he] with g hg
      have hd := gibbsReplicaMean_coordinate_of_integrable μ hH.of_uncurry_left
        (show Measurable (fun x => countableGaussianCovariance v w L x x) from
          hK.comp (measurable_id.prodMk measurable_id)) hg 1 0
      exact congrArg (fun r => r - gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) 2
        (fun x => countableGaussianCovariance v w L (x 1) (x 0))) hd))

lemma gaussianCouplingMean_zero_derivative :
    HasDerivAt (fun b => ∫ g, Real.log (tiltPartition μ (fun x =>
      countableGaussianHamiltonian W v L g x+b*countableGaussianField w L g x) 1) ∂countableGaussianLaw)
      (∫ g, tiltMean μ (countableGaussianHamiltonian W v L g)
        (fun x => countableGaussianCovariance v w L x x) 1 -
      gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) 2
        (fun x => countableGaussianCovariance v w L (x 1) (x 0)) ∂countableGaussianLaw) 0 := by
  have hh := gaussianCouplingMean_derivative μ hW hv hw hL hA hD hE 0
  simp only [zero_mul,add_zero] at hh
  rw [annealedGaussianTiltMean_ibp μ hW hv hw hL hA hD hE] at hh
  exact hh

lemma gaussianCouplingMean_derivative_covariance (a : ℝ) :
    HasDerivAt (fun b => ∫ g, Real.log (tiltPartition μ (fun x =>
      countableGaussianHamiltonian W v L g x+b*countableGaussianField w L g x) 1) ∂countableGaussianLaw)
      (∫ g, tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
        (fun x => countableGaussianCovariance (fun i x => v i x+a*w i x) w L x x) 1 -
      gibbsReplicaMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 2
        (fun x => countableGaussianCovariance (fun i x => v i x+a*w i x) w L (x 1) (x 0)) ∂countableGaussianLaw) a := by
  have hm (i : ℕ) : Measurable (fun x => v i x+a*w i x) := (hv i).add ((hw i).const_mul a)
  have hb (x : S) : (∑ i : Fin (L x), (v i.val x+a*w i.val x)^2)≤2*D+2*a^2*E := by
    simpa only [gaussianTailCoefficient,zero_le,ite_true,one_mul,mul_one,one_pow] using
      gaussianCombinedCoefficient_sq_bound v w L hD hE 1 a 0 x
  have he (g) : countableGaussianHamiltonian W (fun i x => v i x+a*w i x) L g =
      fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x := by
    funext x
    simp only [countableGaussianHamiltonian,countableGaussianField_add,countableGaussianField_smul]
    ring
  have hi := annealedGaussianTiltMean_ibp μ hW hm hw hL hA hb hE
  simp_rw [he] at hi
  exact hi ▸ gaussianCouplingMean_derivative μ hW hv hw hL hA hD hE a

lemma gaussianCouplingMean_difference_bound {B : ℝ} (hB : 0≤B)
    (hC : ∀ a ∈ Icc (0:ℝ) 1, ∀ x y,
      |countableGaussianCovariance (fun i x => v i x+a*w i x) w L x y|≤B) :
    |(∫ g, Real.log (tiltPartition μ (fun x => countableGaussianHamiltonian W v L g x+
      countableGaussianField w L g x) 1) ∂countableGaussianLaw)-
    ∫ g, Real.log (tiltPartition μ (countableGaussianHamiltonian W v L g) 1) ∂countableGaussianLaw|≤2*B := by
  let F := fun a => ∫ g, Real.log (tiltPartition μ (fun x =>
    countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 1) ∂countableGaussianLaw
  let C := fun a => countableGaussianCovariance (fun i x => v i x+a*w i x) w L
  let D' := fun a => ∫ g, tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
        (fun x => C a x x) 1 -
      gibbsReplicaMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 2
        (fun x => C a (x 1) (x 0)) ∂countableGaussianLaw
  have hd (a : ℝ) : HasDerivAt F (D' a) a :=
    gaussianCouplingMean_derivative_covariance μ hW hv hw hL hA hD hE a
  have hb (a) (ha : a ∈ Icc (0:ℝ) 1) : ‖D' a‖≤2*B := by
    have hm : Measurable (Function.uncurry (C a)) := countableGaussianCovariance_measurable
      (fun i => (hv i).add ((hw i).const_mul a)) hw hL
    have hH (g) : Measurable (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) :=
      (countableGaussianHamiltonian_measurable hW hv hL).of_uncurry_left.add
        ((countableGaussianField_measurable hw hL).of_uncurry_left.const_mul a)
    have hdiag (g) : |tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
        (fun x => C a x x) 1|≤B := tiltMean_bound_general μ (hH g)
          (hm.comp (measurable_id.prodMk measurable_id)) hB (fun x => hC a ha x x)
    have hpair (g) : |gibbsReplicaMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 2
        (fun x => C a (x 1) (x 0))|≤B := tiltMean_bound_general _
          (replicaPotential_measurable (hH g) 2)
          (hm.comp ((measurable_pi_apply 1).prodMk (measurable_pi_apply 0))) hB (fun x => hC a ha _ _)
    simpa only [D',probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := countableGaussianLaw) (C := 2*B) (ae_of_all _ fun g => by
        rw [Real.norm_eq_abs]
        exact (abs_sub _ _).trans (by linarith [hdiag g,hpair g]))
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun a (_ : a ∈ Icc (0:ℝ) 1) => (hd a).hasDerivWithinAt) hb (convex_Icc (0:ℝ) 1)
    (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  simpa only [F,one_mul,zero_mul,add_zero,sub_zero,norm_one,mul_one,Real.norm_eq_abs] using hm

end SphericalPerceptronFreeEnergy
end

end OAI
