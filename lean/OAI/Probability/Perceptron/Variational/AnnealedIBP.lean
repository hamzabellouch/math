import Mathlib
import OAI.Probability.Perceptron.Variational.Contact
import OAI.Probability.Perceptron.Interpolation.KernelReplicaGibbs

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceCouplingCovariance (n k : ℕ) (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (j : Fin (n+1)) (x y : NormalizedSpin (n+1)×IndexedLeaf k) :=
  perturbationAmplitude (n+1) (fun _ => 1) j * perturbationAmplitude (n+1) u j *
    sourceJointMonomial p d j x y

lemma sourceCouplingCovariance_measurable (n k r : ℕ) (p d : Fin (n+1) → ℕ)
    (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (i l : Fin r) :
    Measurable (fun x : Fin r → NormalizedSpin (n+1)×IndexedLeaf k =>
      sourceCouplingCovariance n k p d u j (x i) (x l)) := by
  have hh := (sourceReplica_covariance_measurable (N := n+1) (k := k) p d j i l).const_mul
    (perturbationAmplitude (n+1) (fun _ => 1) j * perturbationAmplitude (n+1) u j)
  exact hh

lemma sourceCouplingCovariance_bound (n k : ℕ) (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ)
    (j : Fin (n+1)) (x y : NormalizedSpin (n+1)×IndexedLeaf k) :
    |sourceCouplingCovariance n k p d u j x y| ≤
      |perturbationAmplitude (n+1) (fun _ => 1) j*perturbationAmplitude (n+1) u j| := by
  unfold sourceCouplingCovariance
  rw [abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (sourceJointMonomial_abs_le p d j x y) (abs_nonneg (perturbationAmplitude (n+1) (fun _ => 1) j*perturbationAmplitude (n+1) u j))

lemma sourceCoupling_conditional_ibp (n k r : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (u : Fin (n+1) → ℝ)
    (j : Fin (n+1)) (i : Fin r) (b : SourceBaseData n k)
    {G : (Fin r → NormalizedSpin (n+1)×IndexedLeaf k) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    (∫ g, gibbsReplicaMean (sourceSpinLeafKernel n k b)
      (sourceCouplingHamiltonian n k f p d h u (b,g)) r
      (fun x => sourceCouplingEnergy n k p d h j (b,g) (x i)*G x) ∂countableGaussianLaw) =
    ∫ g, gibbsReplicaMean (sourceSpinLeafKernel n k b)
      (sourceCouplingHamiltonian n k f p d h u (b,g)) r
      (fun x => G x*∑ l, sourceCouplingCovariance n k p d u j (x i) (x l)) -
      r*gibbsReplicaMean (sourceSpinLeafKernel n k b)
      (sourceCouplingHamiltonian n k f p d h u (b,g)) (r+1)
      (fun x => G (fun l => x l.succ)*sourceCouplingCovariance n k p d u j (x i.succ) (x 0))
      ∂countableGaussianLaw := by
  let c := perturbationAmplitude (n+1) (fun _ => 1) j
  have hb := sourceReplica_gaussian_ibp n b.1 k r f (patternPrefix (n+1) b.1 b.2.1)
    p d h hh0 hh u b.2.2 j i hG hB hGB
  dsimp only at hb
  have he := congrArg (fun x : ℝ => c*x) hb
  simp only [sourceSpinLeafKernel_apply,sourceCouplingHamiltonian,sourceCouplingEnergy,
    sourceCouplingCovariance]
  have hs (x : Fin r → NormalizedSpin (n+1)×IndexedLeaf k) :
      G x*∑ l, c*perturbationAmplitude (n+1) u j*sourceJointMonomial p d j (x i) (x l) =
        c*(G x*∑ l, perturbationAmplitude (n+1) u j*sourceJointMonomial p d j (x i) (x l)) := by
    simp only [mul_assoc,Finset.mul_sum]
    ring_nf
  simp only [mul_assoc]
  change (∫ g, gibbsReplicaMean (enrichedIndexedBaseMeasure n k b.2.2)
    (enrichedIndexedHamiltonian n b.1 k f (patternPrefix (n+1) b.1 b.2.1) p d h u g) r
    (fun x => c*(countableGaussianField (sourceGaussianTestRow p d h j)
      (indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) k) g (x i)*G x)) ∂countableGaussianLaw) = _
  simp_rw [replicaMean_const_mul,integral_const_mul]
  rw [hb, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun g => by
    have hs₁ : (fun x : Fin r → NormalizedSpin (n+1)×IndexedLeaf k =>
        G x * ∑ l, c*(perturbationAmplitude (n+1) u j*sourceJointMonomial p d j (x i) (x l))) =
      (fun x => c*(G x*∑ l, perturbationAmplitude (n+1) u j*sourceJointMonomial p d j (x i) (x l))) := by
      funext x
      rw [← Finset.mul_sum]
      ring
    have hs₂ : (fun x : Fin (r+1) → NormalizedSpin (n+1)×IndexedLeaf k =>
        G (fun l => x l.succ)*(c*(perturbationAmplitude (n+1) u j*sourceJointMonomial p d j (x i.succ) (x 0)))) =
      (fun x => c*(G (fun l => x l.succ)*(perturbationAmplitude (n+1) u j*sourceJointMonomial p d j (x i.succ) (x 0)))) := by
      funext x
      ring
    rw [hs₁, hs₂]
    simp only [replicaMean_const_mul]
    ring

lemma sourceCoupling_annealed_ibp (n k r : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (u : Fin (n+1) → ℝ)
    (j : Fin (n+1)) (i : Fin r) (z : Fin k → ℝ) (t : ℝ≥0)
    {G : (Fin r → NormalizedSpin (n+1)×IndexedLeaf k) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B)
    (hYi : Integrable (fun a => tiltMean (sourceSpinLeafKernel n k a.1)
      (sourceCouplingHamiltonian n k f p d h u a)
      (fun x => |sourceCouplingEnergy n k p d h j a x|) 1)
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)) :
    let H := sourceCouplingHamiltonian n k f p d h u
    let Y := sourceCouplingEnergy n k p d h j
    let C := sourceCouplingCovariance n k p d u j
    let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
    (∫ a, gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (H a) r (fun x => Y a (x i)*G x) ∂P) =
      ∫ a, gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (H a) r (fun x => G x*∑ l, C (x i) (x l)) -
        r*gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (H a) (r+1)
          (fun x => G (fun l => x l.succ)*C (x i.succ) (x 0)) ∂P := by
  dsimp only
  let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
  let H := sourceCouplingHamiltonian n k f p d h u
  let Y := sourceCouplingEnergy n k p d h j
  let C := sourceCouplingCovariance n k p d u j
  let C₀ := |perturbationAmplitude (n+1) (fun _ => 1) j*perturbationAmplitude (n+1) u j|
  have hH := sourceCouplingHamiltonian_measurable n k f p d h u
  have hY := sourceCouplingEnergy_measurable n k p d h j
  have he := sourceCoupling_all_exp_ae n k f p d h hh0 hh u j z t
  have he0 : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (sourceSpinLeafKernel n k a.1) := by
    filter_upwards [he] with a ha
    simpa only [zero_mul,add_zero] using ha 0
  have he1 : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)*Y a x) (sourceSpinLeafKernel n k a.1) := by
    filter_upwards [he] with a ha
    simpa only [zero_mul,add_zero,pow_one] using coupling_weighted_power_integrable
      (sourceSpinLeafKernel n k a.1) hH.of_uncurry_left hY.of_uncurry_left ha 0 1
  have hi := kernel_replica_energy_integrable (sourceFullSpinLeafKernel n k) P i hH hY hG he0 he1 hYi hB hGB
  have hmG : Measurable (fun x : Fin (r+1) → NormalizedSpin (n+1)×IndexedLeaf k => G (fun l => x l.succ)) :=
    hG.comp (Measurable.of_eval fun coordinate => measurable_pi_apply coordinate.succ)
  have hsum : ∀ x : Fin r → NormalizedSpin (n+1)×IndexedLeaf k, |∑ l, C (x i) (x l)| ≤ r*C₀ := by
    intro x
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin r, C₀ := Finset.sum_le_sum fun l _ => sourceCouplingCovariance_bound n k p d u j _ _
      _ = _ := by simp
  have h1G : Measurable (fun x : Fin r → NormalizedSpin (n+1)×IndexedLeaf k => G x*∑ l, C (x i) (x l)) :=
    hG.mul (Finset.measurable_sum _ fun l _ => sourceCouplingCovariance_measurable n k r p d u j i l)
  have h2G : Measurable (fun x : Fin (r+1) → NormalizedSpin (n+1)×IndexedLeaf k => G (fun l => x l.succ)*C (x i.succ) (x 0)) :=
    hmG.mul (sourceCouplingCovariance_measurable n k (r+1) p d u j i.succ 0)
  have hi1 := kernel_replicaMean_bounded_integrable (sourceFullSpinLeafKernel n k) P
    (G := fun _ x => G x*∑ l, C (x i) (x l)) hH (h1G.comp measurable_snd)
    (show 0 ≤ B*(r*C₀) by positivity) (fun _ x => by
      rw [abs_mul]; exact mul_le_mul (hGB x) (hsum x) (abs_nonneg _) hB)
  have hi2 := kernel_replicaMean_bounded_integrable (sourceFullSpinLeafKernel n k) P
    (G := fun _ x => G (fun l => x l.succ)*C (x i.succ) (x 0)) hH (h2G.comp measurable_snd)
    (show 0 ≤ B*C₀ by positivity) (fun _ x => by
      rw [abs_mul]; exact mul_le_mul (hGB _) (sourceCouplingCovariance_bound n k p d u j _ _) (abs_nonneg _) hB)
  change (∫ a, gibbsReplicaMean (sourceFullSpinLeafKernel n k a) (H a) r (fun x => Y a (x i)*G x) ∂P) =
    ∫ a, gibbsReplicaMean (sourceFullSpinLeafKernel n k a) (H a) r (fun x => G x*∑ l, C (x i) (x l))-
      r*gibbsReplicaMean (sourceFullSpinLeafKernel n k a) (H a) (r+1) (fun x => G (fun l => x l.succ)*C (x i.succ) (x 0)) ∂P
  have hiR := hi1.sub (hi2.const_mul (r:ℝ))
  dsimp only [sourceFullSpinLeafKernel,Kernel.comap_apply,P,H,Y,C,Pi.sub_apply] at hi hiR ⊢
  have hprodR := integral_prod _ hiR
  simp only [Pi.sub_apply] at hprodR
  rw [integral_prod _ hi, hprodR]
  apply integral_congr_ae
  exact ae_of_all _ fun b => sourceCoupling_conditional_ibp n k r f p d h hh0 hh u j i b hG hB hGB

end SphericalPerceptronFreeEnergy
end

end OAI
