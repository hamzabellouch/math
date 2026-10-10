import Mathlib
import OAI.Probability.IsingPerceptron.GaussianIntegration

namespace OAI

/-! Countable Monomial G G. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

section
variable {S : Type*} [Fintype S]

def replicaEnergyMean {n r : ℕ} (w B : S → ℝ) (A C : S → Fin n → ℝ)
    (D : (Fin (r+1) → S) → ℝ) (g : Fin n → ℝ) : ℝ :=
  ∑ σ, D σ*(linearGaussian A g (σ 0)*replicaGibbs w B C g σ)

def expectedReplicaEnergy {n r : ℕ} (w B : S → ℝ) (A C : S → Fin n → ℝ)
    (D : (Fin (r+1) → S) → ℝ) : ℝ :=
  ∫ g, replicaEnergyMean w B A C D g ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)

def gibbsEnergyMean {n : ℕ} (w B : S → ℝ) (A C : S → Fin n → ℝ)
    (g : Fin n → ℝ) : ℝ := ∑ x, gaussianGibbs w B C g x*linearGaussian A g x

def expectedEnergy {n : ℕ} (w B : S → ℝ) (A C : S → Fin n → ℝ) : ℝ :=
  ∫ g, gibbsEnergyMean w B A C g ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)

def freshCovarianceMean {n r : ℕ} (w B : S → ℝ) (C : S → Fin n → ℝ)
    (κ : S → S → ℝ) (D : (Fin (r+1) → S) → ℝ) (g : Fin n → ℝ) : ℝ :=
  ∑ σ, replicaGibbs w B C g σ*D σ*(∑ z, gaussianGibbs w B C g z*κ (σ 0) z)

def expectedFreshCovariance {n r : ℕ} (w B : S → ℝ) (C : S → Fin n → ℝ)
    (κ : S → S → ℝ) (D : (Fin (r+1) → S) → ℝ) : ℝ :=
  ∫ g, freshCovarianceMean w B C κ D g ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)

lemma integrable_replicaEnergyMean {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin n → ℝ) (D : (Fin (r+1) → S) → ℝ) :
    Integrable (replicaEnergyMean w B A C D) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
  integrable_finsetSum _ (fun σ _ => (integrable_linear_mul_replica hw B A C (σ 0) σ).const_mul (D σ))

lemma expectedReplicaEnergy_const {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin n → ℝ) :
    expectedReplicaEnergy w B A C (fun _ : Fin (r+1) → S => 1) = expectedEnergy w B A C := by
  apply integral_congr_ae
  apply ae_of_all
  intro g
  change (∑ σ : Fin (r+1) → S, 1*(linearGaussian A g (σ 0)*replicaGibbs w B C g σ)) = _
  simpa only [replicaMean, gibbsEnergyMean, one_mul, mul_comm] using
    replicaMean_marginal_zero (r := r) hw B C (linearGaussian A g) g

lemma integrable_gibbsEnergyMean {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin n → ℝ) :
    Integrable (gibbsEnergyMean w B A C) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply integrable_finsetSum
  intro x _
  simpa only [mul_comm] using integrable_linearGaussian_mul_gibbs hw B A C x x

lemma integrable_freshCovarianceMean {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (κ : S → S → ℝ) (D : (Fin (r+1) → S) → ℝ) :
    Integrable (freshCovarianceMean w B C κ D) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hm : AEStronglyMeasurable (freshCovarianceMean w B C κ D)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (continuous_finsetSum _ (fun σ _ => ((continuous_replicaGibbs hw B C σ).mul continuous_const).mul
      (continuous_finsetSum _ (fun z _ => (continuous_gaussianGibbs hw B C z).mul continuous_const)))).aestronglyMeasurable
  apply Integrable.of_bound hm ((∑ σ, |D σ|)*(∑ p : S × S, |κ p.1 p.2|))
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ σ, |replicaGibbs w B C g σ*D σ*(∑ z, gaussianGibbs w B C g z*κ (σ 0) z)| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ σ : Fin (r+1) → S, |D σ| *(∑ p : S × S, |κ p.1 p.2|) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
      have hk := finiteGibbs_average_bound hw (fun x => B x+linearGaussian C g x)
        (κ (σ 0)) (K := ∑ p : S × S, |κ p.1 p.2|) (fun z =>
          Finset.single_le_sum (fun (p : S × S) _ => abs_nonneg (κ p.1 p.2))
            (Finset.mem_univ (σ 0,z)))
      have hprod := mul_le_mul_of_nonneg_right (replicaGibbs_le_one hw B C g σ) (abs_nonneg (D σ))
      exact mul_le_mul (by simpa only [one_mul] using hprod) hk (abs_nonneg _) (abs_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

theorem gaussian_replica_energy_formula {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin (n+1) → ℝ) (κ : S → S → ℝ) (t d : ℝ)
    (hcov : ∀ x y, gaussianCross A C x y = t*κ x y) (hdiag : ∀ x, κ x x = d)
    (D : (Fin (r+1) → S) → ℝ) :
    expectedReplicaEnergy w B A C D = t*(d*expectedReplica w B C D +
      (∑ l : Fin r, expectedReplica w B C (fun σ => D σ*κ (σ 0) (σ l.succ))) -
      (r+1 : ℕ)*expectedFreshCovariance w B C κ D) := by
  rw [expectedReplicaEnergy, show (∫ g, replicaEnergyMean w B A C D g
      ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) = _ from
    gaussian_replica_test_insertion hw B A C D]
  have he (g : Fin (n+1) → ℝ) :
      (∑ σ : Fin (r+1) → S, D σ*(replicaGibbs w B C g σ*
        (∑ l, (gaussianCross A C (σ 0) (σ l)-∑ z, gaussianGibbs w B C g z*gaussianCross A C (σ 0) z)))) =
      t*(d*replicaMean w B C D g+
        (∑ l : Fin r, replicaMean w B C (fun σ => D σ*κ (σ 0) (σ l.succ)) g)-
        (r+1 : ℕ)*freshCovarianceMean w B C κ D g) := by
    simp_rw [hcov]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp_rw [show ∀ σ : Fin (r+1) → S,
      (∑ z, gaussianGibbs w B C g z*(t*κ (σ 0) z)) = t*∑ z, gaussianGibbs w B C g z*κ (σ 0) z by
        intro σ; simp_rw [mul_left_comm (gaussianGibbs w B C g _) t]; rw [Finset.mul_sum]]
    simp_rw [← Finset.mul_sum, Fin.sum_univ_succ, hdiag]
    unfold replicaMean freshCovarianceMean
    rw [Finset.sum_comm]
    simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    congr 1
    · congr 1
      · apply Finset.sum_congr rfl
        intro σ _
        ring
      · apply Finset.sum_congr rfl
        intro σ _
        apply Finset.sum_congr rfl
        intro l _
        ring
    · apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro z _
      ring
  simp_rw [he]
  have hiSum : Integrable (fun g => ∑ l : Fin r,
      replicaMean w B C (fun σ => D σ*κ (σ 0) (σ l.succ)) g)
      (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) :=
    integrable_finsetSum _ (fun l _ => integrable_replicaMean hw B C _)
  simp only [integral_const_mul]
  congr 1
  change (∫ a, (d * replicaMean w B C D a + (∑ l : Fin r, replicaMean w B C (fun σ => D σ * κ (σ 0) (σ l.succ)) a)) -
    (r+1 : ℕ) * freshCovarianceMean w B C κ D a ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) = _
  calc
    _ = (∫ a, d * replicaMean w B C D a +
        (∑ l : Fin r, replicaMean w B C (fun σ => D σ * κ (σ 0) (σ l.succ)) a)
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) -
        ∫ a, (r+1 : ℕ) * freshCovarianceMean w B C κ D a
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1) := by
      exact integral_sub (((integrable_replicaMean hw B C D).const_mul d).add hiSum)
        ((integrable_freshCovarianceMean hw B C κ D).const_mul (r+1 : ℕ))
    _ = _ := by
      congr 1
      · calc
          _ = (∫ a, d * replicaMean w B C D a ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) +
            ∫ a, (∑ l : Fin r, replicaMean w B C (fun σ => D σ * κ (σ 0) (σ l.succ)) a)
              ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1) :=
            integral_add ((integrable_replicaMean hw B C D).const_mul d) hiSum
          _ = _ := by
            rw [integral_const_mul, integral_finsetSum _ (fun l _ => integrable_replicaMean hw B C _)]
            rfl
      · rw [integral_const_mul]
        rfl

lemma expectedReplica_one {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) :
    expectedReplica w B C (fun _ : Fin r → S => 1) = 1 := by
  unfold expectedReplica replicaMean
  simp only [mul_one, replicaGibbs_sum hw]
  simp

def pairCovariance {n : ℕ} (w B : S → ℝ) (C : S → Fin n → ℝ) (κ : S → S → ℝ) : ℝ :=
  expectedFreshCovariance w B C κ (fun _ : Fin 1 → S => 1)

lemma gaussian_single_energy_formula {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin (n+1) → ℝ) (κ : S → S → ℝ) (t d : ℝ)
    (hcov : ∀ x y, gaussianCross A C x y = t*κ x y) (hdiag : ∀ x, κ x x = d) :
    expectedEnergy w B A C = t*(d-pairCovariance w B C κ) := by
  have hh := gaussian_replica_energy_formula (r := 0) hw B A C κ t d hcov hdiag (fun _ => 1)
  simpa [expectedReplicaEnergy_const hw, expectedReplica_one hw, pairCovariance] using hh

theorem gaussian_gg_residual_identity {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin (n+1) → ℝ) (κ : S → S → ℝ) (t d : ℝ)
    (hcov : ∀ x y, gaussianCross A C x y = t*κ x y) (hdiag : ∀ x, κ x x = d)
    (D : (Fin (r+1) → S) → ℝ) :
    t * ((r+1 : ℕ)*expectedFreshCovariance w B C κ D -
      expectedReplica w B C D * pairCovariance w B C κ -
      (∑ l : Fin r, expectedReplica w B C (fun σ => D σ*κ (σ 0) (σ l.succ)))) =
    expectedEnergy w B A C * expectedReplica w B C D - expectedReplicaEnergy w B A C D := by
  rw [gaussian_single_energy_formula hw B A C κ t d hcov hdiag,
    gaussian_replica_energy_formula hw B A C κ t d hcov hdiag]
  ring

def energyFluctuation {n : ℕ} (w B : S → ℝ) (A C : S → Fin n → ℝ) : ℝ :=
  ∫ g, ∑ x, gaussianGibbs w B C g x * |linearGaussian A g x - expectedEnergy w B A C|
    ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)

lemma integrable_gibbs_centered_abs_energy {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin n → ℝ) (m : ℝ) (x : S) :
    Integrable (fun g => gaussianGibbs w B C g x * |linearGaussian A g x-m|)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hi := ((integrable_linearGaussian A x).sub (integrable_const m)).abs.mul_bdd
    (continuous_gaussianGibbs hw B C x).aestronglyMeasurable (c := 1)
    (ae_of_all _ (fun g => by
      rw [Real.norm_eq_abs]
      change |finiteGibbs w (fun x => B x+linearGaussian C g x) x| ≤ 1
      rw [abs_of_nonneg (finiteGibbs_nonneg hw _ x)]
      exact finiteGibbs_le_one hw _ x))
  simpa only [mul_comm, Pi.sub_apply] using hi

lemma energy_covariance_bound {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin n → ℝ) {D : (Fin (r+1) → S) → ℝ}
    {K : ℝ} (hD : ∀ σ, |D σ| ≤ K) :
    |expectedReplicaEnergy w B A C D - expectedEnergy w B A C * expectedReplica w B C D| ≤
      K * energyFluctuation w B A C := by
  let m := expectedEnergy w B A C
  have hi : Integrable (fun g => replicaEnergyMean w B A C D g - m*replicaMean w B C D g)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (integrable_replicaEnergyMean hw B A C D).sub ((integrable_replicaMean hw B C D).const_mul m)
  have hb : Integrable (fun g => K*(∑ x, gaussianGibbs w B C g x*|linearGaussian A g x-m|))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (integrable_finsetSum _ (fun x _ => integrable_gibbs_centered_abs_energy hw B A C m x)).const_mul K
  have he g : replicaEnergyMean w B A C D g - m*replicaMean w B C D g =
      ∑ σ, replicaGibbs w B C g σ*D σ*(linearGaussian A g (σ 0)-m) := by
    simp only [replicaEnergyMean, replicaMean, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  calc
    _ = |∫ g, replicaEnergyMean w B A C D g - m*replicaMean w B C D g
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)| := by
      rw [integral_sub (integrable_replicaEnergyMean hw B A C D)
          ((integrable_replicaMean hw B C D).const_mul m), integral_const_mul]
      rfl
    _ ≤ ∫ g, |replicaEnergyMean w B A C D g - m*replicaMean w B C D g|
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := abs_integral_le_integral_abs
    _ ≤ ∫ g, K*(∑ x, gaussianGibbs w B C g x*|linearGaussian A g x-m|)
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
      apply integral_mono hi.abs hb
      intro g
      dsimp only
      rw [he]
      calc
        _ ≤ ∑ σ, |replicaGibbs w B C g σ*D σ*(linearGaussian A g (σ 0)-m)| :=
          Finset.abs_sum_le_sum_abs ..
        _ ≤ ∑ σ : Fin (r+1) → S, K*(replicaGibbs w B C g σ*|linearGaussian A g (σ 0)-m|) := by
          apply Finset.sum_le_sum
          intro σ _
          rw [abs_mul, abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
          calc
            _ ≤ replicaGibbs w B C g σ*K*|linearGaussian A g (σ 0)-m| := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hD σ) (replicaGibbs_nonneg hw B C g σ)) (abs_nonneg _)
            _ = _ := by ring
        _ = _ := by
          rw [← Finset.mul_sum]
          congr 1
          exact replicaMean_marginal_zero hw B C (fun x => |linearGaussian A g x-m|) g
    _ = _ := by rw [integral_const_mul]; rfl

theorem gaussian_gg_residual_bound {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin (n+1) → ℝ) (κ : S → S → ℝ) (t d : ℝ)
    (hcov : ∀ x y, gaussianCross A C x y = t*κ x y) (hdiag : ∀ x, κ x x = d)
    {D : (Fin (r+1) → S) → ℝ} {K : ℝ} (hD : ∀ σ, |D σ| ≤ K) :
    |t| * |(r+1 : ℕ)*expectedFreshCovariance w B C κ D -
      expectedReplica w B C D * pairCovariance w B C κ -
      (∑ l : Fin r, expectedReplica w B C (fun σ => D σ*κ (σ 0) (σ l.succ)))| ≤
      K * energyFluctuation w B A C := by
  rw [← abs_mul, gaussian_gg_residual_identity hw B A C κ t d hcov hdiag D, abs_sub_comm]
  exact energy_covariance_bound hw B A C hD

end

def referencePartition {X : Type*} [MeasurableSpace X] (ν : Measure X) (H : X → ℝ) : ℝ :=
  ∫ x, Real.exp (H x) ∂ν

def referenceReplicaMean {X : Type*} [MeasurableSpace X] {r : ℕ}
    (ν : Measure X) (H : X → ℝ) (D : (Fin r → X) → ℝ) : ℝ :=
  (∫ σ, Real.exp (∑ i, H (σ i))*D σ ∂Measure.pi (fun _ : Fin r => ν)) /
    (referencePartition ν H)^r

lemma reference_replica_partition {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) (r : ℕ) :
    (∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ => ν)) =
      (referencePartition ν H)^r := by
  simp_rw [Real.exp_sum]
  simpa only [Fintype.card_fin,referencePartition] using
    (integral_fintype_prod_eq_pow (ι := Fin r) (μ := ν) (fun x => Real.exp (H x)))

lemma referenceReplicaMean_eq_ratio {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean ν H D =
      (∫ σ, Real.exp (∑ i, H (σ i))*D σ ∂Measure.pi (fun _ : Fin r => ν)) /
      (∫ σ, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ : Fin r => ν)) := by
  rw [reference_replica_partition]; rfl

lemma finite_reference_weights_sum {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν] :
    ∑ x, ν.real {x} = 1 := by
  have h := integral_fintype (μ := ν) (f := fun _ => (1:ℝ)) Integrable.of_finite
  simpa only [smul_eq_mul,mul_one,integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using h.symm

lemma finite_reference_weight_pos {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν] :
    ∃ x, 0 < ν.real {x} := by
  have hsum := finite_reference_weights_sum ν
  have h := Finset.sum_pos_iff_of_nonneg (fun (x:S) (_:x ∈ Finset.univ) => (measureReal_nonneg : 0 ≤ ν.real {x}))
  obtain ⟨x, _,hx⟩ := h.mp (show 0 < ∑ x, ν.real {x} by rw [hsum]; norm_num)
  exact ⟨x,hx⟩

lemma referencePartition_finite {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsFiniteMeasure ν] (H : S → ℝ) :
    referencePartition ν H = ∑ x, ν.real {x}*Real.exp (H x) := by
  exact integral_fintype Integrable.of_finite

lemma referenceReplicaMean_finite {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsFiniteMeasure ν] (H : S → ℝ)
    {r : ℕ} (D : (Fin r → S) → ℝ) :
    referenceReplicaMean ν H D =
      ∑ σ : Fin r → S, (∏ i, ν.real {σ i}*Real.exp (H (σ i))/referencePartition ν H)*D σ := by
  classical
  rw [referenceReplicaMean, integral_fintype Integrable.of_finite, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [measureReal_def,Measure.pi_singleton,ENNReal.toReal_prod,smul_eq_mul,
    Real.exp_sum,Finset.prod_div_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]
  rw [Finset.prod_mul_distrib]
  ring

lemma referencePartition_map {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    {μ : Measure S} {ν : Measure X} {f : S → X} (hf : MeasurePreserving f μ ν)
    {H : X → ℝ} (hmH : Measurable H) :
    referencePartition μ (H ∘ f) = referencePartition ν H := by
  exact hf.hasLaw.integral_comp hmH.exp.aestronglyMeasurable

lemma referenceReplicaMean_map {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    {μ : Measure S} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : S → X} (hf : MeasurePreserving f μ ν)
    {H : X → ℝ} (hmH : Measurable H) {r : ℕ} {D : (Fin r → X) → ℝ}
    (hmD : Measurable D) :
    referenceReplicaMean μ (H ∘ f) (fun σ => D (fun i => f (σ i))) =
      referenceReplicaMean ν H D := by
  have hpi : MeasurePreserving (fun σ : Fin r → S => fun i => f (σ i))
      (Measure.pi (fun _ : Fin r => μ)) (Measure.pi (fun _ : Fin r => ν)) := by
    refine ⟨Measurable.of_eval (fun index => hf.measurable.comp (measurable_pi_apply index)),?_⟩
    have hmap : IsProbabilityMeasure (μ.map f) := hf.map_eq.symm ▸ inferInstance
    simpa only [hf.map_eq] using Measure.pi_map_pi (μ := fun _ : Fin r => μ) (f := fun _ : Fin r => f) (fun _ : Fin r => hf.measurable.aemeasurable)
  unfold referenceReplicaMean
  rw [referencePartition_map hf hmH]
  congr 1
  exact hpi.hasLaw.integral_comp ((by fun_prop : Measurable
    (fun σ : Fin r → X => Real.exp (∑ i, H (σ i))*D σ)).aestronglyMeasurable)

lemma finite_reference_GibbsReference {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν] :
    GibbsReference (fun x => ν.real {x}) :=
  ⟨fun _ => measureReal_nonneg,finite_reference_weight_pos ν⟩

lemma referenceReplicaMean_eq_finite {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν]
    {n r : ℕ} (B : S → ℝ) (C : S → Fin n → ℝ) (D : (Fin r → S) → ℝ) (g : Fin n → ℝ) :
    referenceReplicaMean ν (fun x => B x+linearGaussian C g x) D =
      replicaMean (fun x => ν.real {x}) B C D g := by
  rw [referenceReplicaMean_finite]
  simp only [referencePartition_finite,replicaMean,replicaGibbs,gaussianGibbs,finiteGibbs,finitePartition]

lemma replicaMean_fresh_eq {S : Type*} [Fintype S] {n r : ℕ}
    (w B : S → ℝ) (C : S → Fin n → ℝ) (κ : S → S → ℝ)
    (D : (Fin (r+1) → S) → ℝ) (g : Fin n → ℝ) :
    replicaMean w B C (fun τ : Fin (r+1+1) → S =>
      D (Fin.tail τ)*κ ((Fin.tail τ) 0) (τ 0)) g = freshCovarianceMean w B C κ D g := by
  classical
  have hp (z:S) (σ:Fin (r+1) → S) : replicaGibbs w B C g (Fin.cons z σ) =
      gaussianGibbs w B C g z*replicaGibbs w B C g σ := by
    simp only [replicaGibbs,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  unfold replicaMean
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r+1+1) => S)),Fintype.sum_prod_type]
  change (∑ z, ∑ σ : Fin (r+1) → S,
    replicaGibbs w B C g (Fin.cons z σ : Fin (r+1+1) → S)*(D σ*κ (σ 0) z)) = _
  simp only [hp]
  rw [Finset.sum_comm]
  unfold freshCovarianceMean
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem finite_gaussian_reference_insertion {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν]
    {n r : ℕ} (B : S → ℝ) (A C : S → Fin (n+1) → ℝ) (D : (Fin (r+1) → S) → ℝ) :
    (∫ g, referenceReplicaMean ν (fun x => B x+linearGaussian C g x)
      (fun σ => linearGaussian A g (σ 0)*D σ) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
    (∫ g, referenceReplicaMean ν (fun x => B x+linearGaussian C g x)
      (fun σ => D σ*(∑ i, gaussianCross A C (σ 0) (σ i)))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) -
    (r+1 : ℕ)*(∫ g, referenceReplicaMean ν (fun x => B x+linearGaussian C g x)
      (fun τ : Fin (r+1+1) → S => D (Fin.tail τ)*gaussianCross A C ((Fin.tail τ) 0) (τ 0))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) := by
  classical
  let w := fun x => ν.real {x}
  have hw : GibbsReference w := finite_reference_GibbsReference ν
  simp_rw [referenceReplicaMean_eq_finite]
  have hi := gaussian_replica_test_insertion hw B A C D
  have he g : (∑ σ : Fin (r+1) → S, D σ*(replicaGibbs w B C g σ*
      (∑ i, (gaussianCross A C (σ 0) (σ i)-∑ z, gaussianGibbs w B C g z*gaussianCross A C (σ 0) z)))) =
      replicaMean w B C (fun σ => D σ*(∑ i, gaussianCross A C (σ 0) (σ i))) g -
      (r+1 : ℕ)*freshCovarianceMean w B C (gaussianCross A C) D g := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    unfold replicaMean freshCovarianceMean
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  have hleft g : (∑ σ : Fin (r+1) → S, D σ*(linearGaussian A g (σ 0)*replicaGibbs w B C g σ)) =
      replicaMean w B C (fun σ => linearGaussian A g (σ 0)*D σ) g := by
    apply Finset.sum_congr rfl
    intro σ _
    ring
  simp_rw [he,hleft] at hi
  rw [integral_sub (integrable_replicaMean hw B C _) ((integrable_freshCovarianceMean hw B C _ D).const_mul _),
    integral_const_mul] at hi
  simpa only [replicaMean_fresh_eq] using hi

lemma gaussian_weighted_sum_law {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    HasLaw (fun g : ι → ℝ => ∑ i, a i * g i)
      (gaussianReal 0 ((∑ i, a i ^ 2).toNNReal))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hi : iIndepFun (fun i => fun g : ι → ℝ => a i * g i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => by fun_prop)
  have hl i : HasLaw (fun g : ι → ℝ => g i) (gaussianReal 0 1)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw
  have hg := hi.hasGaussianLaw_fun_sum (fun i => (gaussianReal_const_mul (hl i) (a i)).hasGaussianLaw)
  refine ⟨(by fun_prop : Measurable (fun g : ι → ℝ => ∑ i, a i * g i)).aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal]
  congr 1
  · have hI i : Integrable (fun g : ι → ℝ => a i * g i)
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
      ((measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).integrable_comp_of_integrable
        ((memLp_id_gaussianReal 1).integrable le_rfl)).const_mul (a i)
    rw [integral_finsetSum _ (fun i _ => hI i)]
    simp_rw [integral_const_mul]
    have hz i : (∫ g : ι → ℝ, g i ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 0 := by
      simpa using (hl i).integral_eq
    simp [hz]
  · congr 1
    have hv i : Var[fun x : ℝ => a i*x; gaussianReal 0 1] = a i^2 := by
      simpa only [id_eq, variance_id_gaussianReal, NNReal.coe_one, mul_one] using
        (variance_const_mul (a i) id (gaussianReal 0 1))
    have hvsum := variance_sum_pi (μ := fun _ : ι => gaussianReal 0 1)
      (X := fun i x => a i * x) (fun i => (memLp_id_gaussianReal 2).const_mul (a i))
    rw [show (∑ i : ι, fun ω : ι → ℝ => a i * ω i) =
      (fun ω => ∑ i, a i * ω i) from by ext; simp] at hvsum
    simpa only [hv] using hvsum

def gaussianCoordinates : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance gaussianCoordinates_probability : IsProbabilityMeasure gaussianCoordinates :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)))

lemma gaussian_prefix_measurePreserving (n : ℕ) :
    MeasurePreserving (fun g : ℕ → ℝ => fun i : Fin n => g i)
      gaussianCoordinates (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  refine ⟨by fun_prop, ?_⟩
  have hi : iIndepFun (fun i : ℕ => fun g : ℕ → ℝ => g i) gaussianCoordinates :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hs := hi.precomp (g := fun i : Fin n => (i:ℕ)) Fin.val_injective
  have he := hs.map_fun_eq_pi_map (fun _ => (by fun_prop : Measurable _).aemeasurable)
  simpa only [gaussianCoordinates,Measure.infinitePi_map_eval] using he

def cylinderField (a : ℕ →₀ ℝ) (g : ℕ → ℝ) : ℝ :=
  a.sum (fun i c => c*g i)

lemma measurable_cylinderField (a : ℕ →₀ ℝ) : Measurable (cylinderField a) := by
  classical
  change Measurable (fun g : ℕ → ℝ => ∑ i ∈ a.support, a i*g i)
  fun_prop

lemma measurable_cylinderFields {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (a : X → ℕ →₀ ℝ) :
    Measurable (fun z : (ℕ → ℝ) × X => cylinderField (a z.2) z.1) :=
  measurable_from_prod_countable_left (fun x => measurable_cylinderField (a x))

lemma cylinderField_eq_prefix (a : ℕ →₀ ℝ) {n : ℕ}
    (ha : ∀ i ∈ a.support, i < n) (g : ℕ → ℝ) :
    cylinderField a g = ∑ i : Fin n, a i*g i := by
  classical
  rw [cylinderField, a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun i c => c*g i) (fun _ _ => zero_mul _)]
  exact (Fin.sum_univ_eq_sum_range _ n).symm

lemma finite_family_support_bound {X : Type*} [Fintype X] (a : X → ℕ →₀ ℝ) :
    ∃ n : ℕ, ∀ x i, a x i ≠ 0 → i < n+1 := by
  classical
  let s := Finset.univ.biUnion (fun x => (a x).support)
  refine ⟨s.sup id,fun x i hi => ?_⟩
  have hm : i ∈ s := Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,Finsupp.mem_support_iff.mpr hi⟩
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)

lemma cylinderField_law (a : ℕ →₀ ℝ) :
    gaussianCoordinates.map (cylinderField a) =
      gaussianReal 0 ((a.sum (fun _ c => c^2)).toNNReal) := by
  classical
  let n := a.support.sup id+1
  have ha : ∀ i ∈ a.support, i < n := fun i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have he : cylinderField a = (fun g : Fin n → ℝ => ∑ i : Fin n, a i*g i) ∘
      (fun g : ℕ → ℝ => fun i : Fin n => g i) := by
    funext g
    exact cylinderField_eq_prefix a ha g
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop),
    (gaussian_prefix_measurePreserving n).map_eq,(gaussian_weighted_sum_law (fun i : Fin n => a i)).map_eq]
  congr 2
  rw [a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun _ c => c^2) (fun _ _ => by norm_num)]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ => a i^2) n

lemma cylinderField_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℝ)
    (g : ℕ → ℝ) : cylinderField (∑ i ∈ s, a i) g = ∑ i ∈ s, cylinderField (a i) g := by
  let L : (ℕ →₀ ℝ) →+ ℝ :=
    { toFun := fun a => cylinderField a g
      map_zero' := by simp [cylinderField]
      map_add' := fun a b => by
        exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul ..) }
  exact map_sum L _ _

lemma cylinder_variance_prefix (a : ℕ →₀ ℝ) {n : ℕ}
    (ha : ∀ i ∈ a.support, i < n) :
    a.sum (fun _ c => c^2) = ∑ i : Fin n, (a i)^2 := by
  rw [a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun _ c => c^2) (fun _ _ => by norm_num)]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => (a i)^2) n).symm

lemma cylinder_variance_sum_le {ι : Type*} [Fintype ι] (a : ι → ℕ →₀ ℝ)
    {K : ℝ} (ha : ∀ i, (a i).sum (fun _ c => c^2) ≤ K) :
    (∑ i, a i).sum (fun _ c => c^2) ≤ (Fintype.card ι : ℝ)^2*K := by
  classical
  obtain ⟨n, hn⟩ := finite_family_support_bound a
  have hs : ∀ j ∈ (∑ i, a i).support, j < n+1 := by
    intro j hj
    by_contra hjn
    have hz i : a i j = 0 := by
      by_contra h
      exact hjn (hn i j h)
    have hz' : (∑ i, a i) j = 0 := by simp only [Finsupp.finsetSum_apply,hz,Finset.sum_const_zero]
    exact Finsupp.mem_support_iff.mp hj hz'
  rw [cylinder_variance_prefix _ hs]
  simp only [Finsupp.finsetSum_apply]
  calc
    _ ≤ ∑ j : Fin (n+1), (Fintype.card ι : ℝ)*(∑ i, (a i j)^2) := by
      apply Finset.sum_le_sum
      intro j _
      simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
        (fun _ => (1:ℝ)) (fun i => a i j)
    _ = (Fintype.card ι : ℝ)*∑ i, ∑ j : Fin (n+1), (a i j)^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ (Fintype.card ι : ℝ)*∑ _i : ι, K := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro i _
      rw [← cylinder_variance_prefix (a i) (fun j hj => hn i j (Finsupp.mem_support_iff.mp hj))]
      exact ha i
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

def cylinderCross (a b : ℕ →₀ ℝ) : ℝ := a.sum (fun i c => c*b i)

lemma cylinderCross_prefix (a b : ℕ →₀ ℝ) {n : ℕ}
    (ha : ∀ i ∈ a.support, i < n) :
    cylinderCross a b = ∑ i : Fin n, a i*b i := by
  rw [cylinderCross,a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun i c => c*b i) (fun _ _ => zero_mul _)]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => a i*b i) n).symm

lemma abs_cylinderCross_le (a b : ℕ →₀ ℝ) :
    |cylinderCross a b| ≤ (a.sum (fun _ c => c^2)+b.sum (fun _ c => c^2))/2 := by
  classical
  let n := a.support.sup id+b.support.sup id+1
  have ha : ∀ i ∈ a.support, i < n := by
    intro i hi
    have := Finset.le_sup (f := id) hi
    dsimp only [id_eq] at this
    omega
  have hb : ∀ i ∈ b.support, i < n := by
    intro i hi
    have := Finset.le_sup (f := id) hi
    dsimp only [id_eq] at this
    omega
  rw [cylinderCross_prefix a b ha,cylinder_variance_prefix a ha,cylinder_variance_prefix b hb]
  calc
    _ ≤ ∑ i : Fin n, |a i*b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, ((a i)^2+(b i)^2)/2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      nlinarith [sq_abs (a i),sq_abs (b i),sq_nonneg (|a i|-|b i|)]
    _ = _ := by rw [← Finset.sum_div,Finset.sum_add_distrib]

lemma measurable_referenceReplicaMean {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] {r : ℕ} {H : Ω × X → ℝ}
    {D : Ω × (Fin r → X) → ℝ} (hmH : Measurable H) (hmD : Measurable D) :
    Measurable (fun ω => referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D (ω,σ))) := by
  have hrep : Measurable (fun z : Ω × (Fin r → X) => ∑ i, H (z.1,z.2 i)) := by
    apply Finset.measurable_sum
    intro i _
    exact hmH.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  exact (hrep.exp.mul hmD).stronglyMeasurable.integral_prod_right'.measurable.div
    (hmH.exp.stronglyMeasurable.integral_prod_right'.measurable.pow_const r)

theorem finite_cylinder_reference_insertion {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν]
    (a b : S → ℕ →₀ ℝ) {r : ℕ} (D : (Fin (r+1) → S) → ℝ) :
    (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates) =
    (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂gaussianCoordinates) -
    (r+1 : ℕ)*(∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun τ : Fin (r+1+1) → S => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂gaussianCoordinates) := by
  classical
  obtain ⟨n₁,hn₁⟩ := finite_family_support_bound a
  obtain ⟨n₂,hn₂⟩ := finite_family_support_bound b
  let n := n₁+n₂
  let C : S → Fin (n+1) → ℝ := fun x i => a x i
  let B : S → Fin (n+1) → ℝ := fun x i => b x i
  have ha x : ∀ i ∈ (a x).support, i < n+1 := by
    intro i hi
    have := hn₁ x i (Finsupp.mem_support_iff.mp hi)
    omega
  have hb x : ∀ i ∈ (b x).support, i < n+1 := by
    intro i hi
    have := hn₂ x i (Finsupp.mem_support_iff.mp hi)
    omega
  have hC (g : ℕ → ℝ) x : linearGaussian C (fun i : Fin (n+1) => g i) x = cylinderField (a x) g :=
    (cylinderField_eq_prefix (a x) (ha x) g).symm
  have hB (g : ℕ → ℝ) x : linearGaussian B (fun i : Fin (n+1) => g i) x = cylinderField (b x) g :=
    (cylinderField_eq_prefix (b x) (hb x) g).symm
  have hcov x y : gaussianCross B C x y = cylinderCross (b x) (a y) :=
    (cylinderCross_prefix (b x) (a y) (hb x)).symm
  have hmC : Measurable (fun z : (Fin (n+1) → ℝ) × S => linearGaussian C z.1 z.2) :=
    measurable_from_prod_countable_left (fun x => by unfold linearGaussian; fun_prop)
  have hmL : Measurable (fun z : (Fin (n+1) → ℝ) × (Fin (r+1) → S) =>
      linearGaussian B z.1 (z.2 0)*D z.2) :=
    measurable_from_prod_countable_left (fun σ => by unfold linearGaussian; fun_prop)
  have hp := (gaussian_prefix_measurePreserving (n+1)).hasLaw
  have hL := hp.integral_comp (measurable_referenceReplicaMean ν hmC hmL).aestronglyMeasurable
  have hR₁ := hp.integral_comp (measurable_referenceReplicaMean ν hmC
    (measurable_of_countable (fun σ : Fin (r+1) → S =>
      D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) |>.comp measurable_snd)).aestronglyMeasurable
  have hR₂ := hp.integral_comp (measurable_referenceReplicaMean ν hmC
    (measurable_of_countable (fun τ : Fin (r+1+1) → S =>
      D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0))) |>.comp measurable_snd)).aestronglyMeasurable
  have hfinite := finite_gaussian_reference_insertion ν (fun _ => 0) B C D
  simp only [zero_add] at hfinite
  simp_rw [hcov] at hfinite
  simp only [Function.comp_apply,hB,hC] at hL hR₁ hR₂
  rw [hL,hR₁,hR₂]
  exact hfinite

end IsingPerceptron

end

end OAI
