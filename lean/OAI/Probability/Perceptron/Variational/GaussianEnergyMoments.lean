import Mathlib
import OAI.Probability.Perceptron.Variational.GaussianBoltzmann
import OAI.Probability.Perceptron.Brownian.GaussianFieldAlgebra

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {S : Type*} [MeasurableSpace S]
variable {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
variable (hL : Measurable L) {A D E : ℝ} (hA : ∀ x, |W x| ≤ A)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)

omit [MeasurableSpace S] in
lemma gaussianHamiltonian_energy_combine (t b : ℝ) (n : ℕ) (g : ℕ → ℝ) (x : S) :
    t*countableGaussianHamiltonian W v L g x+
      b*countableGaussianField (gaussianTailCoefficient w n) L g x =
      countableGaussianHamiltonian (fun x => t*W x)
        (fun i x => t*v i x+b*gaussianTailCoefficient w n i x) L g x := by
  rw [countableGaussianHamiltonian,countableGaussianHamiltonian,countableGaussianField_add,
    countableGaussianField_smul,countableGaussianField_smul]
  ring

omit [MeasurableSpace S] in
lemma gaussianHamiltonian_energy_exp_integrable (t b : ℝ) (n : ℕ) (x : S) :
    Integrable (fun g => Real.exp (t*countableGaussianHamiltonian W v L g x+
      b*countableGaussianField (gaussianTailCoefficient w n) L g x)) countableGaussianLaw := by
  simp_rw [gaussianHamiltonian_energy_combine]
  simpa only [one_mul] using countableGaussianHamiltonian_exp_integrable
    (W := fun x => t*W x) (v := fun i x => t*v i x+b*gaussianTailCoefficient w n i x) (L := L) x 1

include hA hD hE in
omit [MeasurableSpace S] in
lemma gaussianHamiltonian_energy_exp_bound (t b : ℝ) (n : ℕ) (x : S) :
    (∫ g, Real.exp (t*countableGaussianHamiltonian W v L g x+
      b*countableGaussianField (gaussianTailCoefficient w n) L g x) ∂countableGaussianLaw) ≤
      Real.exp (|t| *A+t^2*D+b^2*E) := by
  simp_rw [gaussianHamiltonian_energy_combine]
  have ha (x : S) : |t*W x| ≤ |t| *A := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hA x) (abs_nonneg t)
  have h := countableGaussianHamiltonian_exp_integral_bound
    (v := fun i x => t*v i x+b*gaussianTailCoefficient w n i x) (L := L) ha
    (gaussianCombinedCoefficient_sq_bound v w L hD hE t b n) x 1
  convert h using 1 <;> simp only [one_mul,abs_one,one_pow]
  congr 1
  ring

include hW hv hw hL

lemma gaussianEnergy_weighted_moment_integrable (n k : ℕ) (t : ℝ) (x : S) :
    Integrable (fun g => |countableGaussianField (gaussianTailCoefficient w n) L g x|^k*
      Real.exp (t*countableGaussianHamiltonian W v L g x)) countableGaussianLaw := by
  have hp := gaussianHamiltonian_energy_exp_integrable (W := W) (v := v) (w := w) (L := L) t 1 n x
  have hn := gaussianHamiltonian_energy_exp_integrable (W := W) (v := v) (w := w) (L := L) t (-1) n x
  apply ((hp.add hn).const_mul (k.factorial:ℝ)).mono'
  · exact (((countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL).comp
      (measurable_id.prodMk measurable_const)).abs.pow_const k |>.mul
      (((countableGaussianHamiltonian_measurable hW hv hL).comp
      (measurable_id.prodMk measurable_const)).const_mul t).exp).aestronglyMeasurable
  · exact ae_of_all _ fun g => by
      rw [Real.norm_of_nonneg (by positivity)]
      simpa only [one_mul,neg_one_mul,add_neg_cancel,sub_eq_add_neg,Pi.add_apply] using
        abs_pow_mul_exp_le (t*countableGaussianHamiltonian W v L g x)
          (countableGaussianField (gaussianTailCoefficient w n) L g x) k

include hA hD hE in
lemma gaussianEnergy_weighted_moment_bound (n k : ℕ) (t : ℝ) (x : S) :
    (∫ g, |countableGaussianField (gaussianTailCoefficient w n) L g x|^k*
      Real.exp (t*countableGaussianHamiltonian W v L g x) ∂countableGaussianLaw) ≤
      2*(k.factorial:ℝ)*Real.exp (|t| *A+t^2*D+E) := by
  have hp := gaussianHamiltonian_energy_exp_integrable (W := W) (v := v) (w := w) (L := L) t 1 n x
  have hn := gaussianHamiltonian_energy_exp_integrable (W := W) (v := v) (w := w) (L := L) t (-1) n x
  calc
    _ ≤ ∫ g, (k.factorial:ℝ)*(Real.exp (t*countableGaussianHamiltonian W v L g x+
        1*countableGaussianField (gaussianTailCoefficient w n) L g x)+
        Real.exp (t*countableGaussianHamiltonian W v L g x+
        (-1)*countableGaussianField (gaussianTailCoefficient w n) L g x)) ∂countableGaussianLaw := by
      apply integral_mono (gaussianEnergy_weighted_moment_integrable hW hv hw hL n k t x)
        ((hp.add hn).const_mul _)
      intro g
      simpa only [one_mul,neg_one_mul,sub_eq_add_neg,Pi.add_apply] using abs_pow_mul_exp_le
        (t*countableGaussianHamiltonian W v L g x)
        (countableGaussianField (gaussianTailCoefficient w n) L g x) k
    _ ≤ _ := by
      rw [integral_const_mul,integral_add hp hn]
      have hp' := gaussianHamiltonian_energy_exp_bound hA hD hE t 1 n x
      have hn' := gaussianHamiltonian_energy_exp_bound hA hD hE t (-1) n x
      norm_num only [one_pow,neg_one_sq,one_mul] at hp' hn'
      have hh := mul_le_mul_of_nonneg_left (add_le_add hp' hn') (Nat.cast_nonneg k.factorial : (0:ℝ) ≤ _)
      simp only [one_mul] at *
      nlinarith

variable (μ : Measure S) [IsProbabilityMeasure μ]

include hA hD hE in
lemma gaussianEnergy_weighted_moment_joint_integrable (n k : ℕ) (t : ℝ) :
    Integrable (fun p : S×(ℕ → ℝ) => |countableGaussianField (gaussianTailCoefficient w n) L p.2 p.1|^k*
      Real.exp (t*countableGaussianHamiltonian W v L p.2 p.1)) (μ.prod countableGaussianLaw) := by
  apply integrable_prod_of_nonneg_uniform_integral μ countableGaussianLaw
    ((((countableGaussianField_measurable (gaussianTailCoefficient_measurable hw n) hL).comp measurable_swap).abs.pow_const k).mul
      (((countableGaussianHamiltonian_measurable hW hv hL).comp measurable_swap).const_mul t).exp)
    (fun p => mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le)
    (gaussianEnergy_weighted_moment_integrable hW hv hw hL n k t)
  exact gaussianEnergy_weighted_moment_bound hW hv hw hL hA hD hE n k t

include hA hD hE in
lemma gaussianEnergy_tail_weighted_L2 (t : ℝ) :
    Tendsto (fun n => ∫ p : S×(ℕ → ℝ),
      (countableGaussianField w L p.2 p.1-truncatedCountableGaussianField w L n p.2 p.1)^2*
        Real.exp (t*countableGaussianHamiltonian W v L p.2 p.1) ∂(μ.prod countableGaussianLaw))
      atTop (nhds 0) := by
  have hm (n : ℕ) := gaussianEnergy_weighted_moment_joint_integrable hW hv hw hL hA hD hE μ n 2 t
  have ht := tendsto_integral_of_dominated_convergence (f := fun _ : S => (0:ℝ))
    (fun _ : S => 2*((2:ℕ).factorial:ℝ)*Real.exp (|t| *A+t^2*D+E))
    (fun n => (hm n).integral_prod_left.aestronglyMeasurable) (integrable_const _)
    (fun n => ae_of_all μ fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => by positivity))]
      exact gaussianEnergy_weighted_moment_bound hW hv hw hL hA hD hE n 2 t x)
    (ae_of_all μ fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [truncatedCountableGaussianField_eventually_eq w L x] with n hn
      simp only [countableGaussianField_tail,hn,sub_self,abs_zero,zero_pow (by omega : (2:ℕ)≠0),zero_mul,integral_zero])
  have he (n : ℕ) : (∫ p : S×(ℕ → ℝ),
      (countableGaussianField w L p.2 p.1-truncatedCountableGaussianField w L n p.2 p.1)^2*
        Real.exp (t*countableGaussianHamiltonian W v L p.2 p.1) ∂(μ.prod countableGaussianLaw)) =
      ∫ x, ∫ g, |countableGaussianField (gaussianTailCoefficient w n) L g x|^2*
        Real.exp (t*countableGaussianHamiltonian W v L g x) ∂countableGaussianLaw ∂μ := by
    simpa only [countableGaussianField_tail,sq_abs] using integral_prod _ (hm n)
  simp_rw [he]
  simpa only [integral_zero] using ht

end

lemma integral_mul_le_sqrt_integrals {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    {a b : X → ℝ} (ha : AEStronglyMeasurable a ρ) (hb : AEStronglyMeasurable b ρ)
    (ha0 : ∀ᵐ x ∂ρ, 0 ≤ a x) (hb0 : ∀ᵐ x ∂ρ, 0 ≤ b x)
    (hai : Integrable (fun x => a x^2) ρ) (hbi : Integrable (fun x => b x^2) ρ) :
    (∫ x, a x*b x ∂ρ) ≤ Real.sqrt (∫ x, a x^2 ∂ρ)*Real.sqrt (∫ x, b x^2 ∂ρ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two ha0 hb0
    (by simpa using (memLp_two_iff_integrable_sq ha).mpr hai)
    (by simpa using (memLp_two_iff_integrable_sq hb).mpr hbi)
  simpa only [← Real.sqrt_eq_rpow,Real.rpow_two] using h

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
variable (μ : Measure S) (ν : Measure Ω) [IsProbabilityMeasure μ] [SFinite ν]
variable {H F : Ω → S → ℝ} (hH : Measurable (Function.uncurry H))
variable (hF : Measurable (Function.uncurry F))
variable (hZ : Integrable (fun g => (tiltPartition μ (H g) 1)⁻¹^2) ν)
variable (hI : Integrable (fun p : S×Ω => F p.2 p.1^2*Real.exp (2*H p.2 p.1)) (μ.prod ν))

include hH in
lemma tiltPartition_joint_measurable : Measurable (fun g => tiltPartition μ (H g) 1) := by
  simpa only [tiltPartition,one_mul,Function.uncurry_apply_pair] using
    hH.exp.stronglyMeasurable.integral_prod_right'.measurable

include hH hF hZ hI in
lemma weighted_gibbs_L1_integrable :
    Integrable (fun p : S×Ω => (tiltPartition μ (H p.2) 1)⁻¹*
      (|F p.2 p.1| *Real.exp (H p.2 p.1))) (μ.prod ν) := by
  have ha : AEStronglyMeasurable (fun p : S×Ω => (tiltPartition μ (H p.2) 1)⁻¹) (μ.prod ν) :=
    ((tiltPartition_joint_measurable μ hH).comp measurable_snd).inv.aestronglyMeasurable
  have hb : AEStronglyMeasurable (fun p : S×Ω => |F p.2 p.1| *Real.exp (H p.2 p.1)) (μ.prod ν) :=
    (((hF.comp measurable_swap).abs).mul (hH.comp measurable_swap).exp).aestronglyMeasurable
  have hai : Integrable (fun p : S×Ω => ((tiltPartition μ (H p.2) 1)⁻¹)^2) (μ.prod ν) :=
    measurePreserving_snd.integrable_comp_of_integrable hZ
  have hbi : Integrable (fun p : S×Ω => (|F p.2 p.1| *Real.exp (H p.2 p.1))^2) (μ.prod ν) := by
    simpa only [mul_pow,sq_abs,← Real.exp_nat_mul,Nat.cast_ofNat] using hI
  exact (memLp_two_iff_integrable_sq ha).mpr hai |>.integrable_mul
    ((memLp_two_iff_integrable_sq hb).mpr hbi)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma tiltMean_abs_eq_weighted_integral (g : Ω) :
    tiltMean μ (H g) (fun x => |F g x|) 1 =
      ∫ x, (tiltPartition μ (H g) 1)⁻¹*(|F g x| *Real.exp (H g x)) ∂μ := by
  simp only [tiltMean,tiltIntegral,one_mul,integral_const_mul]
  rw [div_eq_inv_mul]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun _ => mul_comm _ _

include hH hF hZ hI in
lemma tiltMean_abs_annealed_integrable :
    Integrable (fun g => tiltMean μ (H g) (fun x => |F g x|) 1) ν := by
  simp_rw [tiltMean_abs_eq_weighted_integral μ]
  exact (weighted_gibbs_L1_integrable μ ν hH hF hZ hI).integral_prod_right

include hH hF hZ hI in
lemma tiltMean_abs_annealed_L2_bound :
    (∫ g, tiltMean μ (H g) (fun x => |F g x|) 1 ∂ν) ≤
      Real.sqrt (∫ g, (tiltPartition μ (H g) 1)⁻¹^2 ∂ν)*
      Real.sqrt (∫ p : S×Ω, F p.2 p.1^2*Real.exp (2*H p.2 p.1) ∂(μ.prod ν)) := by
  have ha : AEStronglyMeasurable (fun p : S×Ω => (tiltPartition μ (H p.2) 1)⁻¹) (μ.prod ν) :=
    ((tiltPartition_joint_measurable μ hH).comp measurable_snd).inv.aestronglyMeasurable
  have hb : AEStronglyMeasurable (fun p : S×Ω => |F p.2 p.1| *Real.exp (H p.2 p.1)) (μ.prod ν) :=
    (((hF.comp measurable_swap).abs).mul (hH.comp measurable_swap).exp).aestronglyMeasurable
  have hai : Integrable (fun p : S×Ω => ((tiltPartition μ (H p.2) 1)⁻¹)^2) (μ.prod ν) :=
    measurePreserving_snd.integrable_comp_of_integrable hZ
  have hbi : Integrable (fun p : S×Ω => (|F p.2 p.1| *Real.exp (H p.2 p.1))^2) (μ.prod ν) := by
    simpa only [mul_pow,sq_abs,← Real.exp_nat_mul,Nat.cast_ofNat] using hI
  have ha0 : ∀ p : S×Ω, 0 ≤ (tiltPartition μ (H p.2) 1)⁻¹ := by
    intro p
    exact inv_nonneg.mpr (integral_nonneg (fun _ => (Real.exp_pos _).le))
  have hh := integral_mul_le_sqrt_integrals (μ.prod ν) ha hb (ae_of_all _ ha0)
    (ae_of_all _ fun _ => by positivity) hai hbi
  rw [integral_prod _ (weighted_gibbs_L1_integrable μ ν hH hF hZ hI),
    integral_integral_swap (weighted_gibbs_L1_integrable μ ν hH hF hZ hI)] at hh
  simp_rw [← tiltMean_abs_eq_weighted_integral μ] at hh
  have he : (∫ p : S×Ω, (tiltPartition μ (H p.2) 1)⁻¹^2 ∂(μ.prod ν)) =
      ∫ g, (tiltPartition μ (H g) 1)⁻¹^2 ∂ν := by
    rw [integral_prod _ hai]
    simp only [integral_const,probReal_univ,one_smul]
  simpa only [he,mul_pow,sq_abs,← Real.exp_nat_mul,Nat.cast_ofNat] using hh

end SphericalPerceptronFreeEnergy

end

end OAI
