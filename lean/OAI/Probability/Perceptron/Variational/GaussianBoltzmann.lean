import Mathlib
import OAI.Probability.Perceptron.Brownian.CountableGaussianField
import OAI.Probability.Perceptron.Variational.IntegrableGibbs

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section

lemma integrable_prod_of_nonneg_uniform_integral {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [SFinite ν] {F : X×Y → ℝ} {C : ℝ}
    (hF : Measurable F) (hpos : ∀ p, 0 ≤ F p)
    (hi : ∀ x, Integrable (fun y => F (x,y)) ν)
    (hb : ∀ x, (∫ y, F (x,y) ∂ν) ≤ C) : Integrable F (μ.prod ν) := by
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi,?_⟩
  apply (integrable_const C).mono' hF.aestronglyMeasurable.norm.integral_prod_right'
  exact ae_of_all _ fun x => by
    simp only [Real.norm_eq_abs,abs_of_nonneg (hpos _)]
    rw [abs_of_nonneg (integral_nonneg fun y => hpos (x,y))]
    exact hb x

lemma exp_square_sub_bound (a b : ℝ) :
    (Real.exp a-Real.exp b)^2 ≤ 2*Real.exp (2*a)+2*Real.exp (2*b) := by
  rw [show 2*a=a+a by ring,Real.exp_add,show 2*b=b+b by ring,Real.exp_add]
  nlinarith [sq_nonneg (Real.exp a+Real.exp b)]

variable {S : Type*} [MeasurableSpace S]
variable (μ : Measure S) [IsProbabilityMeasure μ]
variable {v : ℕ → S → ℝ} {L : S → ℕ}
variable (hv : ∀ i, Measurable (v i)) (hL : Measurable L)
variable {D : ℝ} (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
include hv hL hD

lemma countableGaussianField_exp_joint_integrable (t : ℝ) :
    Integrable (fun p : S×(ℕ → ℝ) => Real.exp (t*countableGaussianField v L p.2 p.1))
      (μ.prod countableGaussianLaw) := by
  apply integrable_prod_of_nonneg_uniform_integral μ countableGaussianLaw
    (((countableGaussianField_measurable hv hL).comp measurable_swap).const_mul t).exp
    (fun p => (Real.exp_pos _).le)
    (fun x => countableGaussianField_exp_integrable v L x t)
  exact fun x => countableGaussianField_exp_integral_le v L hD x t

lemma truncatedCountableGaussianField_exp_joint_integrable (n : ℕ) (t : ℝ) :
    Integrable (fun p : S×(ℕ → ℝ) =>
      Real.exp (t*truncatedCountableGaussianField v L n p.2 p.1))
      (μ.prod countableGaussianLaw) := by
  apply integrable_prod_of_nonneg_uniform_integral μ countableGaussianLaw
    (((truncatedCountableGaussianField_measurable hv hL n).comp measurable_swap).const_mul t).exp
    (fun p => (Real.exp_pos _).le)
    (fun x => gaussianPrefixField_exp_integrable (maskedGaussianCoefficient v L) n x t)
  exact fun x => truncatedCountableGaussianField_exp_integral_le v L hD n x t

omit hD in
lemma gaussianBoltzmann_difference_sq_integrable (n : ℕ) (t : ℝ) (x : S) :
    Integrable (fun g => (Real.exp (t*truncatedCountableGaussianField v L n g x)-
      Real.exp (t*countableGaussianField v L g x))^2) countableGaussianLaw := by
  apply (((gaussianPrefixField_exp_integrable (maskedGaussianCoefficient v L) n x (2*t)).const_mul 2).add
    ((countableGaussianField_exp_integrable v L x (2*t)).const_mul 2)).mono'
  · exact (((Real.measurable_exp.comp ((measurable_const.mul
      ((truncatedCountableGaussianField_measurable hv hL n).comp (measurable_id.prodMk measurable_const))))).sub
      (Real.measurable_exp.comp (measurable_const.mul
      ((countableGaussianField_measurable hv hL).comp (measurable_id.prodMk measurable_const))))).pow_const 2).aestronglyMeasurable
  · exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs,abs_sq,mul_assoc,Pi.add_apply,truncatedCountableGaussianField] using
        exp_square_sub_bound (t*truncatedCountableGaussianField v L n g x)
          (t*countableGaussianField v L g x)

lemma gaussianBoltzmann_difference_sq_integral_le (n : ℕ) (t : ℝ) (x : S) :
    (∫ g, (Real.exp (t*truncatedCountableGaussianField v L n g x)-
      Real.exp (t*countableGaussianField v L g x))^2 ∂countableGaussianLaw) ≤
        4*Real.exp ((2*t)^2*D/2) := by
  calc
    _ ≤ ∫ g, 2*Real.exp ((2*t)*truncatedCountableGaussianField v L n g x)+
        2*Real.exp ((2*t)*countableGaussianField v L g x) ∂countableGaussianLaw := by
      apply integral_mono (gaussianBoltzmann_difference_sq_integrable hv hL n t x)
        (((gaussianPrefixField_exp_integrable (maskedGaussianCoefficient v L) n x (2*t)).const_mul 2).add
          ((countableGaussianField_exp_integrable v L x (2*t)).const_mul 2))
      intro g
      simpa only [mul_assoc,Pi.add_apply,truncatedCountableGaussianField] using exp_square_sub_bound
        (t*truncatedCountableGaussianField v L n g x) (t*countableGaussianField v L g x)
    _ ≤ _ := by
      change (∫ g, 2*Real.exp ((2*t)*gaussianPrefixField (maskedGaussianCoefficient v L) n g x)+
        2*Real.exp ((2*t)*countableGaussianField v L g x) ∂countableGaussianLaw) ≤ _
      rw [integral_add
        ((gaussianPrefixField_exp_integrable (maskedGaussianCoefficient v L) n x (2*t)).const_mul 2)
        ((countableGaussianField_exp_integrable v L x (2*t)).const_mul 2),integral_const_mul,integral_const_mul]
      have h1 := truncatedCountableGaussianField_exp_integral_le v L hD n x (2*t)
      change (∫ g, Real.exp ((2*t)*gaussianPrefixField (maskedGaussianCoefficient v L) n g x) ∂countableGaussianLaw) ≤ _ at h1
      linarith [countableGaussianField_exp_integral_le v L hD x (2*t)]

lemma gaussianBoltzmann_difference_sq_joint_integrable (n : ℕ) (t : ℝ) :
    Integrable (fun p : S×(ℕ → ℝ) => (Real.exp (t*truncatedCountableGaussianField v L n p.2 p.1)-
      Real.exp (t*countableGaussianField v L p.2 p.1))^2) (μ.prod countableGaussianLaw) := by
  apply integrable_prod_of_nonneg_uniform_integral μ countableGaussianLaw
    (((((truncatedCountableGaussianField_measurable hv hL n).comp measurable_swap).const_mul t).exp.sub
      ((((countableGaussianField_measurable hv hL).comp measurable_swap).const_mul t).exp)).pow_const 2)
    (fun _ => sq_nonneg _) (gaussianBoltzmann_difference_sq_integrable hv hL n t)
  exact gaussianBoltzmann_difference_sq_integral_le hv hL hD n t

lemma gaussianBoltzmann_truncation_L2 (t : ℝ) :
    Tendsto (fun n => ∫ p : S×(ℕ → ℝ),
      (Real.exp (t*truncatedCountableGaussianField v L n p.2 p.1)-
       Real.exp (t*countableGaussianField v L p.2 p.1))^2 ∂(μ.prod countableGaussianLaw))
      atTop (nhds 0) := by
  have hm (n : ℕ) := (gaussianBoltzmann_difference_sq_joint_integrable μ hv hL hD n t)
  simp_rw [integral_prod _ (hm _)]
  have hh := tendsto_integral_of_dominated_convergence (f := fun _ : S => (0 : ℝ))
    (fun _ : S => 4*Real.exp ((2*t)^2*D/2))
    (fun n => (hm n).integral_prod_left.aestronglyMeasurable)
    (integrable_const _)
    (fun n => ae_of_all μ fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
      exact gaussianBoltzmann_difference_sq_integral_le hv hL hD n t x)
    (ae_of_all μ fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [truncatedCountableGaussianField_eventually_eq v L x] with n hn
      simp only [hn,sub_self,zero_pow (by omega : (2 : ℕ)≠0),integral_zero])
  simpa only [integral_zero] using hh

end
variable {S : Type*} [MeasurableSpace S]

def countableGaussianHamiltonian (W : S → ℝ) (v : ℕ → S → ℝ) (L : S → ℕ)
    (g : ℕ → ℝ) (x : S) : ℝ := W x+countableGaussianField v L g x

lemma countableGaussianHamiltonian_measurable {W : S → ℝ} {v : ℕ → S → ℝ} {L : S → ℕ}
    (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hL : Measurable L) :
    Measurable (Function.uncurry (countableGaussianHamiltonian W v L)) :=
  (hW.comp measurable_snd).add (countableGaussianField_measurable hv hL)

variable (μ : Measure S) [IsProbabilityMeasure μ]
variable {W : S → ℝ} {v : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hL : Measurable L)
variable {A D : ℝ} (hA : ∀ x, |W x| ≤ A) (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)

omit [MeasurableSpace S] in
lemma countableGaussianHamiltonian_exp_integrable (x : S) (t : ℝ) :
    Integrable (fun g => Real.exp (t*countableGaussianHamiltonian W v L g x)) countableGaussianLaw := by
  simp only [countableGaussianHamiltonian,mul_add,Real.exp_add]
  exact (countableGaussianField_exp_integrable v L x t).const_mul _

include hA hD in
omit [MeasurableSpace S] in
lemma countableGaussianHamiltonian_exp_integral_bound (x : S) (t : ℝ) :
    (∫ g, Real.exp (t*countableGaussianHamiltonian W v L g x) ∂countableGaussianLaw) ≤
      Real.exp (|t| * A+t^2*D/2) := by
  simp only [countableGaussianHamiltonian,mul_add,Real.exp_add,integral_const_mul]
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hA x) (abs_nonneg t))
  · exact countableGaussianField_exp_integral_le v L hD x t
  · exact integral_nonneg (fun _ => (Real.exp_pos _).le)
  · exact (Real.exp_pos _).le

include hW hv hL hA hD in
lemma countableGaussianHamiltonian_exp_joint_integrable (t : ℝ) :
    Integrable (fun p : S×(ℕ → ℝ) => Real.exp (t*countableGaussianHamiltonian W v L p.2 p.1))
      (μ.prod countableGaussianLaw) := by
  apply integrable_prod_of_nonneg_uniform_integral μ countableGaussianLaw
    (((countableGaussianHamiltonian_measurable hW hv hL).comp measurable_swap).const_mul t).exp
    (fun _ => (Real.exp_pos _).le)
    (fun x => countableGaussianHamiltonian_exp_integrable x t)
  exact fun x => countableGaussianHamiltonian_exp_integral_bound hA hD x t

include hW hv hL hA hD in
lemma countableGaussianHamiltonian_joint_integrable :
    Integrable (fun p : S×(ℕ → ℝ) => countableGaussianHamiltonian W v L p.2 p.1)
      (μ.prod countableGaussianLaw) := by
  apply integrable_of_exp_pos_neg _ ((countableGaussianHamiltonian_measurable hW hv hL).comp measurable_swap)
  · simpa only [one_mul,Function.comp_def,Function.uncurry,Prod.swap] using countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1
  · simpa only [neg_one_mul,Function.comp_def,Function.uncurry,Prod.swap] using countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD (-1)

include hW hv hL hA hD in
lemma countableGaussianHamiltonian_exp_double_integral_bound (t : ℝ) :
    (∫ g, ∫ x, Real.exp (t*countableGaussianHamiltonian W v L g x) ∂μ ∂countableGaussianLaw) ≤
      Real.exp (|t| * A+t^2*D/2) := by
  rw [← integral_integral_swap (countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD t)]
  simpa only [integral_const,probReal_univ,one_smul] using
    integral_mono (countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD t).integral_prod_left
      (integrable_const (Real.exp (|t| * A+t^2*D/2)))
      (fun x => countableGaussianHamiltonian_exp_integral_bound hA hD x t)

include hW hv hL in
lemma gaussianHamiltonianPartition_measurable :
    Measurable (fun g => tiltPartition μ (countableGaussianHamiltonian W v L g) 1) := by
  simpa only [tiltPartition,one_mul,Function.uncurry_apply_pair] using
    (countableGaussianHamiltonian_measurable hW hv hL).exp.stronglyMeasurable.integral_prod_right'.measurable

include hW hv hL hA hD in
lemma gaussianHamiltonianPartition_pos_ae :
    ∀ᵐ g ∂countableGaussianLaw, 0 < tiltPartition μ (countableGaussianHamiltonian W v L g) 1 := by
  filter_upwards [(countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae] with g hg
  exact tilt_partition_pos_of_integrable μ hg

include hW hv hL hA hD in
lemma gaussianHamiltonianPartition_inverse_power_integrable (k : ℕ) :
    Integrable (fun g => (tiltPartition μ (countableGaussianHamiltonian W v L g) 1)⁻¹^k)
      countableGaussianLaw := by
  have hh := countableGaussianHamiltonian_joint_integrable μ hW hv hL hA hD
  have h1 := countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1
  have hk := countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD (-(k:ℝ))
  refine hk.integral_prod_right.mono'
    ((gaussianHamiltonianPartition_measurable μ hW hv hL).inv.pow_const k).aestronglyMeasurable ?_
  filter_upwards [hh.prod_left_ae,h1.prod_left_ae,hk.prod_left_ae,
    gaussianHamiltonianPartition_pos_ae μ hW hv hL hA hD] with g hgi hg1 hgk hgp
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hgp.le) k)]
  exact inverse_partition_power_le μ hgi (by simpa only [one_mul] using hg1) k hgk

include hW hv hL hA hD in
lemma gaussianHamiltonianPartition_inverse_power_bound (k : ℕ) :
    (∫ g, (tiltPartition μ (countableGaussianHamiltonian W v L g) 1)⁻¹^k ∂countableGaussianLaw) ≤
      Real.exp ((k:ℝ)*A+(k:ℝ)^2*D/2) := by
  have hh := countableGaussianHamiltonian_joint_integrable μ hW hv hL hA hD
  have h1 := countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1
  have hk := countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD (-(k:ℝ))
  calc
    _ ≤ ∫ g, ∫ x, Real.exp (-(k:ℝ)*countableGaussianHamiltonian W v L g x) ∂μ ∂countableGaussianLaw := by
      apply integral_mono_ae (gaussianHamiltonianPartition_inverse_power_integrable μ hW hv hL hA hD k)
        hk.integral_prod_right
      filter_upwards [hh.prod_left_ae,h1.prod_left_ae,hk.prod_left_ae] with g hgi hg1 hgk
      exact inverse_partition_power_le μ hgi (by simpa only [one_mul] using hg1) k hgk
    _ ≤ _ := by
      simpa only [abs_neg,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k),neg_sq] using
        countableGaussianHamiltonian_exp_double_integral_bound μ hW hv hL hA hD (-(k:ℝ))

end SphericalPerceptronFreeEnergy

end

end OAI
