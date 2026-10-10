import Mathlib
import OAI.Probability.Perceptron.Variational.EnergyMean

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma sourceCoupling_gg_defect_bound (n k r : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (u : Fin (n+1) → ℝ)
    (j : Fin (n+1)) (i : Fin r) (z : Fin k → ℝ) (t : ℝ≥0)
    {G : (Fin r → NormalizedSpin (n+1)×IndexedLeaf k) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B)
    (hYi : Integrable (fun a => tiltMean (sourceSpinLeafKernel n k a.1)
      (sourceCouplingHamiltonian n k f p d h u a)
      (fun x => |sourceCouplingEnergy n k p d h j a x|) 1)
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw))
    (hci : Integrable (fun a => tiltMean (sourceSpinLeafKernel n k a.1)
      (sourceCouplingHamiltonian n k f p d h u a)
      (fun x => |sourceCouplingEnergy n k p d h j a x-
        ∫ b, tiltMean (sourceSpinLeafKernel n k b.1) (sourceCouplingHamiltonian n k f p d h u b)
          (sourceCouplingEnergy n k p d h j b) 1 ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw|) 1)
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)) :
    let H := sourceCouplingHamiltonian n k f p d h u
    let Y := sourceCouplingEnergy n k p d h j
    let C := sourceCouplingCovariance n k p d u j
    let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
    let EG := ∫ a, gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (H a) r G ∂P
    let EY := ∫ a, tiltMean (sourceSpinLeafKernel n k a.1) (H a) (Y a) 1 ∂P
    let diag := perturbationAmplitude (n+1) (fun _ => 1) j*perturbationAmplitude (n+1) u j*((k:ℝ)/(k+1:ℕ))^(d j)
    |(∫ a, gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (H a) r (fun x => G x*∑ l, C (x i) (x l)) ∂P)-
      diag*EG+EG*(∫ a, gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (H a) 2 (fun x => C (x 1) (x 0)) ∂P)-
      r*(∫ a, gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (H a) (r+1)
        (fun x => G (fun l => x l.succ)*C (x i.succ) (x 0)) ∂P)| ≤
      B*∫ a, tiltMean (sourceSpinLeafKernel n k a.1) (H a) (fun x => |Y a x-EY|) 1 ∂P := by
  dsimp only
  let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
  let H := sourceCouplingHamiltonian n k f p d h u
  let Y := sourceCouplingEnergy n k p d h j
  let C := sourceCouplingCovariance n k p d u j
  let C₀ := |perturbationAmplitude (n+1) (fun _ => 1) j*perturbationAmplitude (n+1) u j|
  let EY := ∫ a, tiltMean (sourceSpinLeafKernel n k a.1) (H a) (Y a) 1 ∂P
  have hH := sourceCouplingHamiltonian_measurable n k f p d h u
  have hY := sourceCouplingEnergy_measurable n k p d h j
  have hexp := sourceCoupling_exp_integrable_ae n k f p d h hh0 hh u j z t
  have hf := kernel_replica_energy_factorization (sourceFullSpinLeafKernel n k) P i hH hY hG
    (hexp.mono fun _ h => h.1) (hexp.mono fun _ h => h.2) hYi EY hci hB hGB
  have he := sourceCoupling_annealed_ibp n k r f p d h hh0 hh u j i z t hG hB hGB hYi
  have hey := sourceCoupling_energy_mean n k f p d h hh0 hh u j z t hYi
  dsimp only at he hey
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
  dsimp only [sourceFullSpinLeafKernel,Kernel.comap_apply,P,H,Y,C] at hi1 hi2 hf
  rw [integral_sub hi1 (hi2.const_mul r),integral_const_mul] at he
  rw [he] at hf
  change EY = _ at hey
  apply le_trans ?_ hf
  apply le_of_eq
  congr 1
  rw [hey]
  ring

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) (P : Measure A) (H : A → S → ℝ)

def kernelGGDefect (C : S → S → ℝ) (diag : ℝ) (r : ℕ) (i : Fin r)
    (G : (Fin r → S) → ℝ) : ℝ :=
  (∫ a, gibbsReplicaMean (κ a) (H a) r (fun x => G x*∑ l, C (x i) (x l)) ∂P)-
    diag*(∫ a, gibbsReplicaMean (κ a) (H a) r G ∂P)+
    (∫ a, gibbsReplicaMean (κ a) (H a) r G ∂P)*
      (∫ a, gibbsReplicaMean (κ a) (H a) 2 (fun x => C (x 1) (x 0)) ∂P)-
    r*(∫ a, gibbsReplicaMean (κ a) (H a) (r+1)
      (fun x => G (fun l => x l.succ)*C (x i.succ) (x 0)) ∂P)

lemma kernelGGDefect_const_mul [IsMarkovKernel κ] (C : S → S → ℝ) (diag c : ℝ) (r : ℕ) (i : Fin r)
    (G : (Fin r → S) → ℝ) :
    kernelGGDefect κ P H (fun x y => c*C x y) (c*diag) r i G =
      c*kernelGGDefect κ P H C diag r i G := by
  have hs : (fun x : Fin r → S => G x*∑ l, c*C (x i) (x l)) =
      (fun x => c*(G x*∑ l, C (x i) (x l))) := by
    funext x
    rw [← Finset.mul_sum]
    ring
  have hp : (fun x : Fin (r+1) → S => G (fun l => x l.succ)*(c*C (x i.succ) (x 0))) =
      (fun x => c*(G (fun l => x l.succ)*C (x i.succ) (x 0))) := by
    funext x
    ring
  unfold kernelGGDefect
  rw [hs,hp]
  simp only [replicaMean_const_mul,integral_const_mul]
  ring

end

lemma source_contact_joint_gg_error (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0)
    {H T c a s : ℝ} (hH : 0 ≤ H) (hhH : h 0 ≤ H) (ht : (t:ℝ) ≤ T) (hs : 0<s)
    (hu : ∀ l, u l ∈ Icc 1 2)
    (hup : ∀ l, (u+Pi.single j s : Fin (n+1) → ℝ) l ∈ Icc 1 2) (hum : ∀ l, (u+Pi.single j (-s) : Fin (n+1) → ℝ) l ∈ Icc 1 2)
    (hmin : IsLocalMin (fun r => c*(r-a)^2-
      ∫ b, sourceKernelPressure n k f p d (u+Pi.single j r) h b
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw) 0)
    (hp : c*(0-a)^2-(∫ b, sourceKernelPressure n k f p d u h b
      ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw) ≤ c*(s-a)^2-
      ∫ b, sourceKernelPressure n k f p d (u+Pi.single j s) h b
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (hm : c*(0-a)^2-(∫ b, sourceKernelPressure n k f p d u h b
      ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw) ≤ c*(-s-a)^2-
      ∫ b, sourceKernelPressure n k f p d (u+Pi.single j (-s)) h b
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (r : ℕ) (i : Fin r) {G : (Fin r → NormalizedSpin (n+1)×IndexedLeaf k) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    |kernelGGDefect (sourceFullSpinLeafKernel n k)
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
      (sourceCouplingHamiltonian n k f p d h u) (sourceJointMonomial p d j)
      (((k:ℝ)/(k+1:ℕ))^(d j)) r i G| ≤
      (B*(Real.sqrt (2*c)/Real.sqrt (1/(n+1:ℕ))+
        (c*s+4*Real.sqrt (enrichedVarianceConstant k z f H T/(n+1:ℕ))/s)/(1/(n+1:ℕ))))/
      (perturbationAmplitude (n+1) (fun _ => 1) j*perturbationAmplitude (n+1) u j) := by
  have hc := source_contact_energy_concentration n k f p d h hh0 hh u j z hz hz0 hz1 t
    hH hhH ht hs hu hup hum hmin hp hm
  dsimp only at hc
  have hb := sourceCoupling_gg_defect_bound n k r f p d h hh0 hh u j i z t hG hB hGB hc.1 hc.2.1
  dsimp only at hb
  let A := perturbationAmplitude (n+1) (fun _ => 1) j*perturbationAmplitude (n+1) u j
  have hA : 0 < A := by
    dsimp [A,perturbationAmplitude,perturbationScale]
    have huj : 0 < u j := lt_of_lt_of_le zero_lt_one (hu j).1
    positivity
  have hscale := kernelGGDefect_const_mul (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (sourceCouplingHamiltonian n k f p d h u) (sourceJointMonomial p d j)
    (((k:ℝ)/(k+1:ℕ))^(d j)) A r i G
  change |kernelGGDefect (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (sourceCouplingHamiltonian n k f p d h u) (fun x y => A*sourceJointMonomial p d j x y)
    (A*(((k:ℝ)/(k+1:ℕ))^(d j))) r i G| ≤ _ at hb
  rw [hscale,abs_mul,abs_of_pos hA] at hb
  rw [le_div_iff₀ hA,mul_comm]
  exact hb.trans (mul_le_mul_of_nonneg_left hc.2.2 hB)

end SphericalPerceptronFreeEnergy

end

end OAI
