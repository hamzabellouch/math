import Mathlib
import OAI.Probability.Perceptron.Interpolation.ReplicaIBP
import OAI.Probability.Perceptron.Variational.UnboundedContact

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ]

lemma kernelReplica_measurable (n : ℕ) :
    Measurable (fun a => Measure.pi (fun _ : Fin n => κ a)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm isPiSystem_pi
  rintro _ ⟨s,hs,rfl⟩
  simp_rw [Measure.pi_pi]
  exact Finset.measurable_prod _ fun i _ => κ.measurable_coe (hs i (mem_univ i))

def kernelReplica (n : ℕ) : Kernel A (Fin n → S) :=
  ⟨(fun a => Measure.pi (fun _ : Fin n => κ a)),kernelReplica_measurable κ n⟩

instance (n : ℕ) : IsMarkovKernel (kernelReplica κ n) := ⟨fun _ => by
  change IsProbabilityMeasure (Measure.pi _)
  infer_instance⟩

lemma kernel_replicaMean_measurable {H : A → S → ℝ} {n : ℕ} {G : A → (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hG : Measurable (Function.uncurry G)) :
    Measurable (fun a => gibbsReplicaMean (κ a) (H a) n (G a)) := by
  change Measurable (fun a => tiltMean (kernelReplica κ n a) (replicaPotential (H a) n) (G a) 1)
  apply kernel_tiltMean_measurable (kernelReplica κ n) (H := fun a => replicaPotential (H a) n) _ hG
  change Measurable (fun a : A × (Fin n → S) => ∑ i, H a.1 (a.2 i))
  exact Finset.measurable_sum _ fun i _ => hH.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

lemma kernel_replicaMean_bounded_integrable (P : Measure A) [IsFiniteMeasure P]
    {H : A → S → ℝ} {n : ℕ} {G : A → (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hG : Measurable (Function.uncurry G))
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ a x, |G a x| ≤ B) :
    Integrable (fun a => gibbsReplicaMean (κ a) (H a) n (G a)) P := by
  apply Integrable.of_bound (kernel_replicaMean_measurable κ hH hG).aestronglyMeasurable B
  exact ae_of_all _ fun a => by
    simpa only [Real.norm_eq_abs,gibbsReplicaMean] using tiltMean_bound_general (Measure.pi fun _ : Fin n => κ a)
      (replicaPotential_measurable hH.of_uncurry_left n) hG.of_uncurry_left hB (hGB a)

lemma kernel_replica_energy_integrable (P : Measure A)
    {H Y : A → S → ℝ} {n : ℕ} (j : Fin n) {G : (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) (hG : Measurable G)
    (he : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a))
    (hi : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)*Y a x) (κ a))
    (hYi : Integrable (fun a => tiltMean (κ a) (H a) (fun x => |Y a x|) 1) P)
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Integrable (fun a => gibbsReplicaMean (κ a) (H a) n (fun x => Y a (x j)*G x)) P := by
  apply (hYi.const_mul B).mono'
    (kernel_replicaMean_measurable κ hH ((hY.comp (measurable_fst.prodMk
      ((measurable_pi_apply j).comp measurable_snd))).mul (hG.comp measurable_snd))).aestronglyMeasurable
  filter_upwards [he,hi] with a he hi
  simpa only [Real.norm_eq_abs] using replicaMean_energy_bound (κ a) j hH.of_uncurry_left
    hY.of_uncurry_left hG he hi hB hGB

lemma kernel_replica_energy_factorization (P : Measure A) [IsProbabilityMeasure P]
    {H Y : A → S → ℝ} {n : ℕ} (j : Fin n) {G : (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) (hG : Measurable G)
    (he : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a))
    (hi : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)*Y a x) (κ a))
    (hYi : Integrable (fun a => tiltMean (κ a) (H a) (fun x => |Y a x|) 1) P)
    (c : ℝ) (hci : Integrable (fun a => tiltMean (κ a) (H a) (fun x => |Y a x-c|) 1) P)
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    |(∫ a, gibbsReplicaMean (κ a) (H a) n (fun x => Y a (x j)*G x) ∂P) -
      c*(∫ a, gibbsReplicaMean (κ a) (H a) n G ∂P)| ≤
      B*∫ a, tiltMean (κ a) (H a) (fun x => |Y a x-c|) 1 ∂P := by
  have hI := kernel_replica_energy_integrable κ P j hH hY hG he hi hYi hB hGB
  have hGI := kernel_replicaMean_bounded_integrable κ P (G := fun _ => G) hH (hG.comp measurable_snd) hB (fun _ => hGB)
  rw [← integral_const_mul,← integral_sub hI (hGI.const_mul c),← integral_const_mul]
  calc
    _ ≤ ∫ a, |gibbsReplicaMean (κ a) (H a) n (fun x => Y a (x j)*G x) -
        c*gibbsReplicaMean (κ a) (H a) n G| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun a => gibbsReplicaMean (κ a) (H a) n (fun x => Y a (x j)*G x) -
          c*gibbsReplicaMean (κ a) (H a) n G)
    _ ≤ _ := by
      apply integral_mono_ae (hI.sub (hGI.const_mul c)).abs (hci.const_mul B)
      filter_upwards [he,hi] with a he hi
      have hci' := he.mul_const c
      have hs := replicaMean_energy_sub (κ a) j hH.of_uncurry_left hY.of_uncurry_left
        measurable_const hG he hi hci' hGB
      rw [replicaMean_const_mul] at hs
      simp only [Pi.sub_apply] at *
      rw [← hs]
      have hii : Integrable (fun x => Real.exp (H a x)*(Y a x-c)) (κ a) :=
        (hi.sub hci').congr (ae_of_all _ fun x => by dsimp; ring)
      exact replicaMean_energy_bound (κ a) j hH.of_uncurry_left (hY.of_uncurry_left.sub measurable_const)
        hG he hii hB hGB

end

lemma sourceJointMonomial_measurable {N k : ℕ} (p d : Fin N → ℕ) (j : Fin N) :
    Measurable (Function.uncurry (sourceJointMonomial (k := k) p d j)) := by
  have ht : Measurable (fun a : (NormalizedSpin N×IndexedLeaf k)×(NormalizedSpin N×IndexedLeaf k) =>
      ((indexedCommonDepth k a.2.2 a.1.2).val:ℝ)/(k+1:ℕ)) := by
    exact (Measurable.of_discrete (f := fun a : IndexedLeaf k×IndexedLeaf k =>
      ((indexedCommonDepth k a.1 a.2).val:ℝ)/(k+1:ℕ))).comp (measurable_snd.snd.prodMk measurable_fst.snd)
  have hr : Measurable (fun a : (NormalizedSpin N×IndexedLeaf k)×(NormalizedSpin N×IndexedLeaf k) =>
      spinOverlap a.1.1 a.2.1) := by
    exact (measurable_subtype_coe.comp measurable_fst.fst).inner
      (measurable_subtype_coe.comp measurable_snd.fst)
  exact (ht.pow_const _).mul (hr.pow_const _)

lemma sourceJointMonomial_abs_le {N k : ℕ} (p d : Fin N → ℕ) (j : Fin N)
    (x y : NormalizedSpin N×IndexedLeaf k) : |sourceJointMonomial p d j x y| ≤ 1 := by
  have ht0 : 0 ≤ ((indexedCommonDepth k y.2 x.2).val:ℝ)/(k+1:ℕ) := by positivity
  have ht1 : ((indexedCommonDepth k y.2 x.2).val:ℝ)/(k+1:ℕ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast (indexedCommonDepth k y.2 x.2).isLt.le
  rw [sourceJointMonomial,abs_mul,abs_pow,abs_pow,abs_of_nonneg ht0]
  exact (mul_le_of_le_one_left (by positivity) (pow_le_one₀ ht0 ht1)).trans
    (pow_le_one₀ (abs_nonneg _) (spinOverlap_abs_le _ _))

lemma sourceReplica_covariance_measurable {N k r : ℕ} (p d : Fin N → ℕ) (j : Fin N)
    (i l : Fin r) : Measurable (fun x : Fin r → NormalizedSpin N×IndexedLeaf k =>
      sourceJointMonomial p d j (x i) (x l)) := by
  have hs : Measurable (fun x : Fin r → NormalizedSpin N×IndexedLeaf k => (x i,x l)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply l)
  have hm := (sourceJointMonomial_measurable (N := N) (k := k) p d j).comp hs
  exact hm

end SphericalPerceptronFreeEnergy

end

end OAI
