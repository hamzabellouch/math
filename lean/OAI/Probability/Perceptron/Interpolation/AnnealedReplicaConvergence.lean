import Mathlib
import OAI.Probability.Perceptron.Variational.IndexedAncestry
import OAI.Probability.Perceptron.Interpolation.CountableGaussianReplicaIBP

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
variable (μ : Measure S) (ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
variable {H : Ω → S → ℝ} (hH : Measurable (Function.uncurry H))

include hH in
lemma annealedReplica_bounded_integrable {r : ℕ} {G : (Fin r → S) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Integrable (fun g => gibbsReplicaMean μ (H g) r G) ν := by
  apply Integrable.of_bound (replicaMean_varying_measurable μ (F := fun _ => G) hH (hG.comp measurable_snd)).aestronglyMeasurable B
  exact ae_of_all _ fun g => by
    simpa only [Real.norm_eq_abs,gibbsReplicaMean] using tiltMean_bound_general (Measure.pi fun _ : Fin r => μ) (H := replicaPotential (H g) r)
      (replicaPotential_measurable (hH.comp (measurable_const.prodMk measurable_id)) r) hG hB hGB

include hH in
lemma annealedReplica_bounded_tendsto {r : ℕ} {F : ℕ → (Fin r → S) → ℝ} {G : (Fin r → S) → ℝ}
    (hF : ∀ n, Measurable (F n)) (_ : Measurable G) {B : ℝ} (hB : 0 ≤ B)
    (hFB : ∀ n x, |F n x| ≤ B) (hlim : ∀ x, Tendsto (fun n => F n x) atTop (nhds (G x)))
    (he : ∀ᵐ g ∂ν, Integrable (fun x => Real.exp (H g x)) μ) :
    Tendsto (fun n => ∫ g, gibbsReplicaMean μ (H g) r (F n) ∂ν) atTop
      (nhds (∫ g, gibbsReplicaMean μ (H g) r G ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => B)
    (fun n => (replicaMean_varying_measurable μ (F := fun _ => F n) hH ((hF n).comp measurable_snd)).aestronglyMeasurable)
    (integrable_const B)
  · intro n
    exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs,gibbsReplicaMean] using tiltMean_bound_general (Measure.pi fun _ : Fin r => μ) (H := replicaPotential (H g) r)
        (replicaPotential_measurable (hH.comp (measurable_const.prodMk measurable_id)) r) (hF n) hB (hFB n)
  · filter_upwards [he] with g hg
    have hh : Measurable (H g) := hH.comp (measurable_const.prodMk measurable_id)
    let := tilt_law_probability_of_integrable μ (by simpa only [one_mul] using hg :
      Integrable (fun x => Real.exp (1*H g x)) μ)
    simp_rw [gibbsReplicaMean_integral_of_integrable μ hh hg]
    exact tendsto_integral_of_dominated_convergence (fun _ : Fin r → S => B)
      (fun n => (hF n).aestronglyMeasurable) (integrable_const B)
      (fun n => ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFB n x)
      (ae_of_all _ hlim)

end
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma gaussianReplica_prefix_ibp (m n : ℕ) (j : Fin n)
    {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ} {G : (Fin n → S) → ℝ}
    (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
    (hL : Measurable L) (hG : Measurable G) {A D E B : ℝ}
    (hA : ∀ x, |W x| ≤ A) (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
    (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)
    (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    let H := countableGaussianHamiltonian W v L
    (∫ g, gibbsReplicaMean μ (H g) n (fun x => truncatedCountableGaussianField w L m g (x j)*G x)
      ∂countableGaussianLaw) =
    ∫ g, gibbsReplicaMean μ (H g) n (fun x => G x*∑ l, gaussianPrefixCovariance v w L m (x j) (x l)) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => G (fun l => x l.succ)*gaussianPrefixCovariance v w L m (x j.succ) (x 0)) ∂countableGaussianLaw := by
  dsimp only
  let H := countableGaussianHamiltonian W v L
  let a := maskedGaussianCoefficient v L
  let b := maskedGaussianCoefficient w L
  let C := Real.sqrt D
  let Q := Real.sqrt E
  have hmH : Measurable (Function.uncurry H) := countableGaussianHamiltonian_measurable hW hv hL
  have hmHg (g) : Measurable (H g) := hmH.comp (measurable_const.prodMk measurable_id)
  have hma (i) : Measurable (a i) := maskedGaussianCoefficient_measurable hv hL i
  have hmb (i) : Measurable (b i) := maskedGaussianCoefficient_measurable hw hL i
  have ha (i x) : |a i x| ≤ C := maskedGaussianCoefficient_bound v L hD i x
  have hb (i x) : |b i x| ≤ Q := maskedGaussianCoefficient_bound w L hE i x
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have he : ∀ᵐ g ∂countableGaussianLaw, Integrable (fun x => Real.exp (H g x)) μ := by
    simpa only [one_mul] using (countableGaussianHamiltonian_exp_joint_integrable μ hW hv hL hA hD 1).prod_left_ae
  let F (i : Fin m) (x : Fin n → S) := b i.val (x j)*G x
  let U (i : Fin m) (x : Fin n → S) := replicaPotential (a i.val) n x*F i x
  let V (i : Fin m) (x : Fin (n+1) → S) := a i.val (x 0)*(b i.val (x j.succ)*G (fun l => x l.succ))
  have hFm (i) : Measurable (F i) := ((hmb i.val).comp (measurable_pi_apply j)).mul hG
  have hUm (i) : Measurable (U i) := (replicaPotential_measurable (hma i.val) n).mul (hFm i)
  have hVm (i) : Measurable (V i) := by
    exact ((hma i.val).comp (measurable_pi_apply 0)).mul
      (((hmb i.val).comp (measurable_pi_apply j.succ)).mul
        (hG.comp (Measurable.of_eval fun index : Fin n => measurable_pi_apply index.succ)))
  have hFB (i x) : |F i x| ≤ Q*B := by
    exact (abs_mul _ _).trans_le (mul_le_mul (hb _ _) (hGB _) (abs_nonneg _) hQ)
  have hUB (i x) : |U i x| ≤ (n:ℝ)*C*Q*B := by
    dsimp only [U]
    rw [abs_mul]
    calc
      _ ≤ ((n:ℝ)*C)*(Q*B) := mul_le_mul (replicaPotential_bound (ha i.val) n x) (hFB i x)
        (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg n) hC)
      _ = _ := by ring
  have hVB (i x) : |V i x| ≤ C*Q*B := by
    dsimp only [V]
    rw [abs_mul]
    calc
      _ ≤ C*(Q*B) := mul_le_mul (ha _ _) (hFB i (fun l => x l.succ)) (abs_nonneg _) hC
      _ = _ := by ring
  have hUi (i) : Integrable (fun g => gibbsReplicaMean μ (H g) n (U i)) countableGaussianLaw :=
    annealedReplica_bounded_integrable μ countableGaussianLaw hmH (hUm i) (by positivity) (hUB i)
  have hVi (i) : Integrable (fun g => gibbsReplicaMean μ (H g) (n+1) (V i)) countableGaussianLaw :=
    annealedReplica_bounded_integrable μ countableGaussianLaw hmH (hVm i) (by positivity) (hVB i)
  have hFi (i : Fin m) : Integrable (fun g => g i.val*gibbsReplicaMean μ (H g) n (F i)) countableGaussianLaw := by
    have hg : Integrable (fun g : ℕ → ℝ => g i.val) countableGaussianLaw :=
      (measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianReal 0 1) i.val).integrable_comp_of_integrable
        ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))
    apply hg.mul_bdd (replicaMean_measurable μ hmH (hFm i)).aestronglyMeasurable
    exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs,gibbsReplicaMean] using tiltMean_bound_general _
        (replicaPotential_measurable (hmHg g) n) (hFm i) (mul_nonneg hQ hB) (hFB i)
  have hleft : ∀ᵐ g ∂countableGaussianLaw,
      gibbsReplicaMean μ (H g) n (fun x => truncatedCountableGaussianField w L m g (x j)*G x) =
        ∑ i : Fin m, g i.val*gibbsReplicaMean μ (H g) n (F i) := by
    filter_upwards [he] with g hg
    rw [show (fun x => truncatedCountableGaussianField w L m g (x j)*G x) =
      fun x => ∑ i : Fin m, g i.val*F i x by
        funext x
        simp only [truncatedCountableGaussianField,gaussianPrefixField,Finset.sum_mul,F,b]
        apply Finset.sum_congr rfl
        intro i _
        ring]
    rw [gibbsReplicaMean_sum_of_integrable μ Finset.univ (hmHg g) hg
      (fun i _ => (hFm i).const_mul (g i.val)) (D := fun i => |g i.val| *(Q*B))
      (fun i _ x => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hFB i x) (abs_nonneg _))]
    simp_rw [replicaMean_const_mul]
  have hright : ∀ᵐ g ∂countableGaussianLaw,
      (∑ i : Fin m, (gibbsReplicaMean μ (H g) n (U i)-(n:ℝ)*gibbsReplicaMean μ (H g) (n+1) (V i))) =
      gibbsReplicaMean μ (H g) n (fun x => G x*∑ l, gaussianPrefixCovariance v w L m (x j) (x l)) -
      n*gibbsReplicaMean μ (H g) (n+1)
        (fun x => G (fun l => x l.succ)*gaussianPrefixCovariance v w L m (x j.succ) (x 0)) := by
    filter_upwards [he] with g hg
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,
      ← gibbsReplicaMean_sum_of_integrable μ Finset.univ (hmHg g) hg (fun i _ => hUm i) (fun i _ => hUB i),
      ← gibbsReplicaMean_sum_of_integrable μ Finset.univ (hmHg g) hg (fun i _ => hVm i) (fun i _ => hVB i)]
    congr 1
    · congr 1
      funext x
      dsimp [U,F,replicaPotential,gaussianPrefixCovariance,a,b]
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro i _
      ring
    · congr 1
      congr 1
      funext x
      simp only [V,gaussianPrefixCovariance,Finset.mul_sum,a,b]
      apply Finset.sum_congr rfl
      intro i _
      ring
  calc
    _ = ∫ g, ∑ i : Fin m, g i.val*gibbsReplicaMean μ (H g) n (F i) ∂countableGaussianLaw :=
      integral_congr_ae hleft
    _ = ∑ i : Fin m, ∫ g, g i.val*gibbsReplicaMean μ (H g) n (F i) ∂countableGaussianLaw :=
      integral_finsetSum _ (fun i _ => hFi i)
    _ = ∑ i : Fin m, ∫ g, gibbsReplicaMean μ (H g) n (U i)-
        n*gibbsReplicaMean μ (H g) (n+1) (V i) ∂countableGaussianLaw := by
      apply Finset.sum_congr rfl
      intro i _
      exact gaussianHamiltonian_replica_coordinate_ibp μ i.val n hW hv hL (hFm i) hA hD
        (mul_nonneg hQ hB) (hFB i)
    _ = ∫ g, ∑ i : Fin m, (gibbsReplicaMean μ (H g) n (U i)-
        n*gibbsReplicaMean μ (H g) (n+1) (V i)) ∂countableGaussianLaw :=
      (integral_finsetSum _ (fun i _ => (hUi i).sub ((hVi i).const_mul n))).symm
    _ = _ := integral_congr_ae hright

end SphericalPerceptronFreeEnergy

end

end OAI
