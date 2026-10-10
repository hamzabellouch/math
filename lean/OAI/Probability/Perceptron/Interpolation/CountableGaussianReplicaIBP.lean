import Mathlib
import OAI.Probability.Perceptron.Pressure.GaussianHamiltonianCoordinates
import OAI.Probability.Perceptron.Variational.CountableGaussianIBP

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma countableGaussian_replica_coordinate_ibp (i n : ℕ)
    {H : (ℕ → ℝ) → S → ℝ} {v : S → ℝ} {G : (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hv : Measurable v) (hG : Measurable G)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hGD : ∀ x, |G x| ≤ D)
    (haff : ∀ g t x, H (Function.update g i t) x = H (Function.update g i 0) x+t*v x)
    (hi : ∀ᵐ g ∂countableGaussianLaw, Integrable (fun x => Real.exp (H g x)) μ) :
    (∫ g, g i*gibbsReplicaMean μ (H g) n G ∂countableGaussianLaw) =
      ∫ g, gibbsReplicaMean μ (H g) n (fun x => replicaPotential v n x*G x)-
        n*gibbsReplicaMean μ (H g) (n+1) (fun x => v (x 0)*G (fun l => x l.succ))
        ∂countableGaussianLaw := by
  let Hr (g : ℕ → ℝ) := replicaPotential (H g) n
  have hHr : Measurable (Function.uncurry Hr) := by
    change Measurable (fun p : (ℕ → ℝ)×(Fin n → S) => ∑ l, H p.1 (p.2 l))
    exact Finset.measurable_sum _ fun l _ => hH.comp
      (measurable_fst.prodMk ((measurable_pi_apply l).comp measurable_snd))
  have hvr := replicaPotential_measurable hv n
  have hir : ∀ᵐ g ∂countableGaussianLaw, Integrable (fun x => Real.exp (Hr g x))
      (Measure.pi fun _ : Fin n => μ) := by
    filter_upwards [hi] with g hg
    simpa only [one_mul] using replica_exp_integrable μ (by simpa only [one_mul] using hg :
      Integrable (fun x => Real.exp (1*H g x)) μ) n
  have haffr (g : ℕ → ℝ) (t : ℝ) (x : Fin n → S) :
      Hr (Function.update g i t) x = Hr (Function.update g i 0) x+t*replicaPotential v n x := by
    calc
      _ = ∑ l, (H (Function.update g i 0) (x l)+t*v (x l)) :=
        Finset.sum_congr rfl (fun l _ => haff g t (x l))
      _ = _ := by simp only [Hr,replicaPotential,Finset.sum_add_distrib,Finset.mul_sum]
  have hh := countableGaussian_coordinate_tilt_ibp_of_exp_integrable
    (Measure.pi fun _ : Fin n => μ) i hHr hvr hG (mul_nonneg (Nat.cast_nonneg n) hC) hD
    (replicaPotential_bound hvC n) hGD haffr hir
  change (∫ g, g i*gibbsReplicaMean μ (H g) n G ∂countableGaussianLaw) =
    ∫ g, gibbsReplicaMean μ (H g) n (fun x => replicaPotential v n x*G x)-
      gibbsReplicaMean μ (H g) n G*gibbsReplicaMean μ (H g) n (replicaPotential v n)
      ∂countableGaussianLaw at hh
  refine hh.trans ?_
  apply integral_congr_ae
  filter_upwards [hi] with g hg
  have hHg : Measurable (H g) := hH.comp (measurable_const.prodMk measurable_id)
  rw [gibbsReplicaMean_potential_of_integrable μ hHg hv hg hvC,
    gibbsReplicaMean_product_of_integrable μ hHg hv hG hg hvC hGD]
  ring

lemma gaussianHamiltonian_replica_coordinate_ibp (i n : ℕ)
    {W : S → ℝ} {v : ℕ → S → ℝ} {L : S → ℕ} {G : (Fin n → S) → ℝ}
    (hW : Measurable W) (hv : ∀ j, Measurable (v j)) (hL : Measurable L) (hG : Measurable G)
    {A D B : ℝ} (hA : ∀ x, |W x| ≤ A)
    (hD : ∀ x, (∑ j : Fin (L x), v j.val x^2) ≤ D)
    (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    let H := countableGaussianHamiltonian W v L
    let a := maskedGaussianCoefficient v L i
    (∫ g, g i*gibbsReplicaMean μ (H g) n G ∂countableGaussianLaw) =
      ∫ g, gibbsReplicaMean μ (H g) n (fun x => replicaPotential a n x*G x)-
        n*gibbsReplicaMean μ (H g) (n+1) (fun x => a (x 0)*G (fun l => x l.succ))
        ∂countableGaussianLaw := by
  dsimp only
  apply countableGaussian_replica_coordinate_ibp μ i n
    (countableGaussianHamiltonian_measurable hW hv hL)
    (maskedGaussianCoefficient_measurable hv hL i) hG (Real.sqrt_nonneg D) hB
    (maskedGaussianCoefficient_bound v L hD i) hGB
    (fun g t x => countableGaussianHamiltonian_update W v L g i t x)
  simpa only [one_mul] using
    (countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae

lemma integrable_tiltLaw_of_weighted {H F : S → ℝ} (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) μ)
    (hF : Integrable (fun x => Real.exp (H x)*F x) μ) : Integrable F (tiltLaw μ H 1) := by
  have hp := tilt_partition_pos_of_integrable μ (by simpa only [one_mul] using he :
    Integrable (fun x => Real.exp (1*H x)) μ)
  unfold tiltLaw
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hp)))
  apply (integrable_withDensity_iff_integrable_smul' (hH.const_mul 1).exp.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [one_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul] using hF

lemma replicaMean_varying_measurable {Ω : Type*} [MeasurableSpace Ω] {H : Ω → S → ℝ}
    {n : ℕ} {F : Ω → (Fin n → S) → ℝ} (hH : Measurable (Function.uncurry H))
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun g => gibbsReplicaMean μ (H g) n (F g)) := by
  have hr : Measurable (fun p : Ω×(Fin n → S) => Real.exp (replicaPotential (H p.1) n p.2)) := by
    apply Measurable.exp
    exact Finset.measurable_sum _ fun i _ => hH.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  let ρ := Measure.pi fun _ : Fin n => μ
  have hn : Measurable (fun g => ∫ x, Real.exp (replicaPotential (H g) n x)*F g x ∂ρ) :=
    (hr.mul hF).stronglyMeasurable.integral_prod_right'.measurable
  have hd : Measurable (fun g => ∫ x, Real.exp (replicaPotential (H g) n x) ∂ρ) :=
    hr.stronglyMeasurable.integral_prod_right'.measurable
  unfold gibbsReplicaMean tiltMean tiltIntegral tiltPartition
  simp only [one_mul]
  convert hn.div hd using 1

lemma replicaMean_energy_bound {H F : S → ℝ} {n : ℕ} (j : Fin n)
    {G : (Fin n → S) → ℝ} (hH : Measurable H) (hF : Measurable F) (hG : Measurable G)
    (he : Integrable (fun x => Real.exp (H x)) μ)
    (hFint : Integrable (fun x => Real.exp (H x)*F x) μ)
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    |gibbsReplicaMean μ H n (fun x => F (x j)*G x)| ≤ B*tiltMean μ H (fun x => |F x|) 1 := by
  have he1 : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using he
  let := tilt_law_probability_of_integrable μ he1
  let θ := tiltLaw μ H 1
  let ρ := Measure.pi fun _ : Fin n => θ
  have hFi : Integrable F θ := integrable_tiltLaw_of_weighted μ hH he hFint
  have hcoord : Integrable (fun x : Fin n → S => F (x j)) ρ :=
    (measurePreserving_eval (fun _ : Fin n => θ) j).integrable_comp_of_integrable hFi
  have hprod : Integrable (fun x : Fin n → S => F (x j)*G x) ρ := by
    apply (hcoord.abs.const_mul B).mono' ((hF.comp (measurable_pi_apply j)).mul hG).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      change |F (x j)*G x| ≤ B*|F (x j)|
      rw [abs_mul,mul_comm |F (x j)|]
      exact mul_le_mul (hGB x) le_rfl (abs_nonneg _) hB
  rw [gibbsReplicaMean_integral_of_integrable μ hH he]
  calc
    _ ≤ ∫ x : Fin n → S, |F (x j)*G x| ∂ρ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ρ) (fun x : Fin n → S => F (x j)*G x)
    _ ≤ ∫ x : Fin n → S, B*|F (x j)| ∂ρ := by
      apply integral_mono hprod.abs (hcoord.abs.const_mul B)
      intro x
      change |F (x j)*G x| ≤ B*|F (x j)|
      rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hGB x) (abs_nonneg (F (x j)))]
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      rw [← gibbsReplicaMean_coordinate_of_integrable μ hH hF.abs he n j,
        gibbsReplicaMean_integral_of_integrable μ hH he]

lemma replicaMean_energy_sub {H F Q : S → ℝ} {n : ℕ} (j : Fin n)
    {G : (Fin n → S) → ℝ} (hH : Measurable H) (hF : Measurable F) (hQ : Measurable Q) (hG : Measurable G)
    (he : Integrable (fun x => Real.exp (H x)) μ)
    (hFint : Integrable (fun x => Real.exp (H x)*F x) μ)
    (hQint : Integrable (fun x => Real.exp (H x)*Q x) μ)
    {B : ℝ} (hGB : ∀ x, |G x| ≤ B) :
    gibbsReplicaMean μ H n (fun x => (F (x j)-Q (x j))*G x) =
      gibbsReplicaMean μ H n (fun x => F (x j)*G x)-gibbsReplicaMean μ H n (fun x => Q (x j)*G x) := by
  have he1 : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using he
  let := tilt_law_probability_of_integrable μ he1
  let θ := tiltLaw μ H 1
  let ρ := Measure.pi fun _ : Fin n => θ
  have him (f : S → ℝ) (hf : Measurable f) (hfi : Integrable (fun x => Real.exp (H x)*f x) μ) :
      Integrable (fun x : Fin n → S => f (x j)*G x) ρ := by
    have hc := (measurePreserving_eval (fun _ : Fin n => θ) j).integrable_comp_of_integrable
      (integrable_tiltLaw_of_weighted μ hH he hfi)
    apply (hc.abs.const_mul B).mono' ((hf.comp (measurable_pi_apply j)).mul hG).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      change |f (x j)*G x| ≤ B*|f (x j)|
      rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hGB x) (abs_nonneg (f (x j)))]
  simp_rw [gibbsReplicaMean_integral_of_integrable μ hH he,sub_mul]
  exact integral_sub (him F hF hFint) (him Q hQ hQint)

end SphericalPerceptronFreeEnergy

end

end OAI
