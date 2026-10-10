import Mathlib
import OAI.Probability.SphericalField.Gibbs.Tilting

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
section Replicas
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma replica_partition {v : S → ℝ} (_hv : Measurable v) (n : ℕ) (t : ℝ) :
    tiltPartition (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) t =
      (tiltPartition μ v t)^n := by
  unfold tiltPartition replicaPotential
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * v x))]
  simp

lemma replica_mean_potential {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (n : ℕ) (t : ℝ) :
    tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) (replicaPotential v n) t =
      n * tiltMean μ v v t := by
  have hd := tilt_partition_deriv (Measure.pi fun _ : Fin n => μ)
    (replicaPotential_measurable hv n) (mul_nonneg (Nat.cast_nonneg n) hC)
    (replicaPotential_bound hvC n) t
  have he : tiltPartition (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) =
      fun u => (tiltPartition μ v u)^n := funext (replica_partition μ hv n)
  rw [he] at hd
  have hg := (tilt_partition_deriv μ hv hC hvC t).pow n
  have hder := hd.unique hg
  unfold tiltMean
  rw [hder,replica_partition μ hv n]
  have hp := (tilt_partition_pos μ hv hC hvC t).ne'
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_sub_one,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp

lemma gaussian_replica_integrationByParts {v : S → ℝ} {n : ℕ} {F : (Fin n → S) → ℝ}
    (hv : Measurable v) (hF : Measurable F) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) :
    (∫ t, t * tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) F t
      ∂gaussianReal 0 1) =
    ∫ t, tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n)
        (fun x => replicaPotential v n x * F x) t - n *
      tiltMean (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) F t *
      tiltMean μ v v t ∂gaussianReal 0 1 := by
  rw [gaussian_tilt_integrationByParts _ (replicaPotential_measurable hv n) hF
    (mul_nonneg (Nat.cast_nonneg n) hC) hD (replicaPotential_bound hvC n) hFD]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    dsimp only
    rw [replica_mean_potential μ hv hC hvC n t]
    ring

end Replicas

section GibbsProducts
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_law_apply {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ)
    {s : Set S} (hs : MeasurableSet s) :
    tiltLaw μ v t s = (ENNReal.ofReal (tiltPartition μ v t))⁻¹ *
      ENNReal.ofReal (∫ x in s, Real.exp (t * v x) ∂μ) := by
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC
      (by norm_num : (0:ℝ) ≤ 1) hvC (fun _ => by norm_num) t
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ fun x => (Real.exp_pos _).le)]

lemma tilt_law_pi {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (n : ℕ) (t : ℝ) :
    tiltLaw (Measure.pi fun _ : Fin n => μ) (replicaPotential v n) t =
      Measure.pi (fun _ : Fin n => tiltLaw μ v t) := by
  have := tilt_law_probability μ hv hC hvC t
  symm
  apply Measure.pi_eq
  intro s hs
  rw [tilt_law_apply _ (replicaPotential_measurable hv n)
    (mul_nonneg (Nat.cast_nonneg n) hC) (replicaPotential_bound hvC n) t (MeasurableSet.univ_pi hs),
    replica_partition μ hv n,ENNReal.ofReal_pow (tilt_partition_pos μ hv hC hvC t).le,
    Measure.restrict_pi_pi]
  have he (x : Fin n → S) : Real.exp (t * replicaPotential v n x) =
      ∏ i, Real.exp (t * v (x i)) := by
    simp only [replicaPotential,Finset.mul_sum,Real.exp_sum]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (f := fun (_ : Fin n) x => Real.exp (t * v x)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))]
  simp_rw [tilt_law_apply μ hv hC hvC t (hs _)]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.inv_pow]

lemma tilt_mean_twice {v w F : S → ℝ} (hw : Measurable w)
    {D : ℝ} (hD : 0 ≤ D) (hwD : ∀ x, |w x| ≤ D) (s t : ℝ) :
    tiltMean (tiltLaw μ w s) v F t = tiltMean μ (fun x => s*w x+t*v x) F 1 := by
  have := tilt_law_probability μ hw hD hwD s
  have hp := (tilt_partition_pos μ hw hD hwD s).ne'
  unfold tiltMean tiltIntegral tiltPartition
  rw [tilt_law_integral μ hw hD hwD s,tilt_law_integral μ hw hD hwD s]
  simp only [tiltMean,tiltIntegral,one_mul,Real.exp_add]
  have he (x : S) : Real.exp (s*w x) * (Real.exp (t*v x)*F x) =
      Real.exp (s*w x) * Real.exp (t*v x) * F x := by ring
  simp_rw [he]
  change ((∫ x, Real.exp (s*w x) * Real.exp (t*v x) * F x ∂μ) / tiltPartition μ w s) /
    ((∫ x, Real.exp (s*w x) * Real.exp (t*v x) ∂μ) / tiltPartition μ w s) = _
  rw [div_div_div_cancel_right₀ hp]

end GibbsProducts

lemma gaussian_pi_coordinate_integrationByParts (n : ℕ) (i : Fin (n+1))
    {F D : (Fin (n+1) → ℝ) → ℝ} (hF : Measurable F) (hD : Measurable D)
    {C B : ℝ} (hFC : ∀ g, |F g| ≤ C) (hDB : ∀ g, |D g| ≤ B)
    (hd : ∀ (g : Fin n → ℝ) (t : ℝ),
      HasDerivAt (fun u => F (i.insertNth u g)) (D (i.insertNth t g)) t) :
    (∫ g, g i * F g ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ g, D g ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  let ν : Measure (Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm
  have hmF : Measurable (fun p : ℝ × (Fin n → ℝ) => F (i.insertNth p.1 p.2)) :=
    hF.comp e.measurable
  have hmD : Measurable (fun p : ℝ × (Fin n → ℝ) => D (i.insertNth p.1 p.2)) :=
    hD.comp e.measurable
  have hiF : Integrable (fun p : ℝ × (Fin n → ℝ) => p.1 * F (i.insertNth p.1 p.2))
      ((gaussianReal 0 1).prod ν) := by
    apply ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).comp_fst ν |>.mul_bdd
      hmF.aestronglyMeasurable
    exact ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hFC (i.insertNth p.1 p.2)
  have hiD : Integrable (fun p : ℝ × (Fin n → ℝ) => D (i.insertNth p.1 p.2))
      ((gaussianReal 0 1).prod ν) :=
    Integrable.of_bound hmD.aestronglyMeasurable B
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hDB (i.insertNth p.1 p.2))
  rw [← he.integral_comp e.measurableEmbedding (fun g => g i * F g),
    ← he.integral_comp e.measurableEmbedding D]
  change (∫ p : ℝ × (Fin n → ℝ), ((i.insertNth p.1 p.2 : Fin (n+1) → ℝ) i) *
    F (i.insertNth p.1 p.2) ∂(gaussianReal 0 1).prod ν) =
      ∫ p : ℝ × (Fin n → ℝ), D (i.insertNth p.1 p.2) ∂(gaussianReal 0 1).prod ν
  simp only [Fin.insertNth_apply_same]
  rw [integral_prod_symm _ hiF,integral_prod_symm _ hiD]
  apply integral_congr_ae
  exact ae_of_all _ fun g => standardGaussian_integrationByParts (hd g)
    (hmD.comp (measurable_id.prodMk measurable_const))
    (fun t => hFC (i.insertNth t g)) (fun t => hDB (i.insertNth t g))

end SphericalPerceptron
end
end

end OAI
