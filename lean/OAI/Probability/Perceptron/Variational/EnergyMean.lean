import Mathlib
import OAI.Probability.Perceptron.Pressure.KernelEnergyConcentration
import OAI.Probability.Perceptron.Variational.AnnealedIBP

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma gibbsReplicaMean_const_of_integrable {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {H : S → ℝ} (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) μ) (r : ℕ) (c : ℝ) :
    gibbsReplicaMean μ H r (fun _ => c) = c := by
  let := tilt_law_probability_of_integrable μ (by simpa only [one_mul] using he :
    Integrable (fun x => Real.exp (1*H x)) μ)
  rw [gibbsReplicaMean_integral_of_integrable μ hH he]
  simp

lemma sourceCoupling_exp_integrable_ae (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (u : Fin (n+1) → ℝ)
    (j : Fin (n+1)) (z : Fin k → ℝ) (t : ℝ≥0) :
    ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw,
      Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x)) (sourceSpinLeafKernel n k a.1) ∧
        Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x)*
          sourceCouplingEnergy n k p d h j a x) (sourceSpinLeafKernel n k a.1) := by
  have hH := sourceCouplingHamiltonian_measurable n k f p d h u
  have hY := sourceCouplingEnergy_measurable n k p d h j
  filter_upwards [sourceCoupling_all_exp_ae n k f p d h hh0 hh u j z t] with a ha
  constructor
  · simpa only [zero_mul,add_zero] using ha 0
  · simpa only [zero_mul,add_zero,pow_one] using coupling_weighted_power_integrable
      (sourceSpinLeafKernel n k a.1) hH.of_uncurry_left hY.of_uncurry_left ha 0 1

lemma sourceCoupling_energy_mean (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (u : Fin (n+1) → ℝ)
    (j : Fin (n+1)) (z : Fin k → ℝ) (t : ℝ≥0)
    (hYi : Integrable (fun a => tiltMean (sourceSpinLeafKernel n k a.1)
      (sourceCouplingHamiltonian n k f p d h u a)
      (fun x => |sourceCouplingEnergy n k p d h j a x|) 1)
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)) :
    let H := sourceCouplingHamiltonian n k f p d h u
    let Y := sourceCouplingEnergy n k p d h j
    let C := sourceCouplingCovariance n k p d u j
    let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
    (∫ a, tiltMean (sourceSpinLeafKernel n k a.1) (H a) (Y a) 1 ∂P) =
      perturbationAmplitude (n+1) (fun _ => 1) j*perturbationAmplitude (n+1) u j*
        ((k:ℝ)/(k+1:ℕ))^(d j)-
      ∫ a, gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (H a) 2 (fun x => C (x 1) (x 0)) ∂P := by
  dsimp only
  let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
  let H := sourceCouplingHamiltonian n k f p d h u
  let C := sourceCouplingCovariance n k p d u j
  let D := perturbationAmplitude (n+1) (fun _ => 1) j*perturbationAmplitude (n+1) u j*((k:ℝ)/(k+1:ℕ))^(d j)
  have he := sourceCoupling_annealed_ibp n k 1 f p d h hh0 hh u j 0 z t
    (G := fun _ => 1) measurable_const (by norm_num : (0:ℝ) ≤ 1) (fun _ => by norm_num) hYi
  dsimp only at he
  simp only [mul_one,one_mul,Fin.sum_univ_one,Nat.cast_one,Fin.succ_zero_eq_one] at he
  have hAe := sourceCoupling_exp_integrable_ae n k f p d h hh0 hh u j z t
  have hleft : (fun a => gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (H a) 1
      (fun x => sourceCouplingEnergy n k p d h j a (x 0))) =ᵐ[P]
      (fun a => tiltMean (sourceSpinLeafKernel n k a.1) (H a) (sourceCouplingEnergy n k p d h j a) 1) := by
    filter_upwards [hAe] with a ha
    exact gibbsReplicaMean_coordinate_of_integrable _ (sourceCouplingHamiltonian_section n k f p d h u a)
      (sourceCouplingEnergy_section n k p d h j a) ha.1 1 0
  have hdiag : ∀ x : NormalizedSpin (n+1)×IndexedLeaf k, C x x = D := by
    intro x
    dsimp [C,sourceCouplingCovariance,D]
    rw [sourceJointMonomial_diagonal]
  have hright : (fun a => gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (H a) 1
      (fun x => C (x 0) (x 0))) =ᵐ[P] (fun _ => D) := by
    filter_upwards [hAe] with a ha
    simp only [hdiag]
    exact gibbsReplicaMean_const_of_integrable _ (sourceCouplingHamiltonian_section n k f p d h u a) ha.1 1 D
  have hI := kernel_replicaMean_bounded_integrable (sourceFullSpinLeafKernel n k) P
    (H := H) (G := fun _ (x : Fin 2 → NormalizedSpin (n+1)×IndexedLeaf k) => C (x 1) (x 0))
    (sourceCouplingHamiltonian_measurable n k f p d h u)
    ((sourceCouplingCovariance_measurable n k 2 p d u j 1 0).comp measurable_snd)
    (abs_nonneg _) (fun _ x => sourceCouplingCovariance_bound n k p d u j _ _)
  dsimp only [sourceFullSpinLeafKernel,Kernel.comap_apply] at hI
  rw [integral_congr_ae hleft] at he
  have hr : (∫ a, gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (H a) 1
      (fun x => C (x 0) (x 0))-gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (H a) 2
      (fun x => C (x 1) (x 0)) ∂P) =
      D-∫ a, gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (H a) 2 (fun x => C (x 1) (x 0)) ∂P := by
    calc
      _ = ∫ a, D-gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (H a) 2 (fun x => C (x 1) (x 0)) ∂P := by
        apply integral_congr_ae
        filter_upwards [hright] with a ha
        rw [ha]
      _ = _ := by rw [integral_sub (integrable_const _) hI]; simp
  exact he.trans hr

lemma source_contact_energy_concentration (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
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
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw) :
    let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
    let H₀ := sourceCouplingHamiltonian n k f p d h u
    let Y := sourceCouplingEnergy n k p d h j
    let EY := ∫ b, tiltMean (sourceSpinLeafKernel n k b.1) (H₀ b) (Y b) 1 ∂P
    Integrable (fun b => tiltMean (sourceSpinLeafKernel n k b.1) (H₀ b) (fun x => |Y b x|) 1) P ∧
      Integrable (fun b => tiltMean (sourceSpinLeafKernel n k b.1) (H₀ b) (fun x => |Y b x-EY|) 1) P ∧
      (∫ b, tiltMean (sourceSpinLeafKernel n k b.1) (H₀ b) (fun x => |Y b x-EY|) 1 ∂P) ≤
        Real.sqrt (2*c)/Real.sqrt (1/(n+1:ℕ))+
          (c*s+4*Real.sqrt (enrichedVarianceConstant k z f H T/(n+1:ℕ))/s)/(1/(n+1:ℕ)) := by
  have hc := source_contact_thermal_disorder n k f p d h hh0 hh u j z hz hz0 hz1 t
    hH hhH ht hs hu hup hum hmin hp hm
  dsimp only at hc ⊢
  have hmean : Integrable (fun b => (1/(n+1:ℕ))*tiltMean (sourceSpinLeafKernel n k b.1)
      (sourceCouplingHamiltonian n k f p d h u b) (sourceCouplingEnergy n k p d h j b) 1)
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) := by
    have hm := hc.2.1
    change Integrable (fun b => (1/(n+1:ℕ))*tiltMean (sourceSpinLeafKernel n k b.1)
      (fun x => sourceCouplingHamiltonian n k f p d h u b x+0*sourceCouplingEnergy n k p d h j b x)
      (sourceCouplingEnergy n k p d h j b) 1) _ at hm
    simpa only [zero_mul,add_zero] using hm
  have htherm := hc.1.integrable (by norm_num : (1:ENNReal) ≤ 2)
  change Integrable (fun b => Real.sqrt (1/(n+1:ℕ))*tiltMean (sourceSpinLeafKernel n k b.1)
    (fun x => sourceCouplingHamiltonian n k f p d h u b x+0*sourceCouplingEnergy n k p d h j b x)
    (fun x => |sourceCouplingEnergy n k p d h j b x-tiltMean (sourceSpinLeafKernel n k b.1)
      (fun x => sourceCouplingHamiltonian n k f p d h u b x+0*sourceCouplingEnergy n k p d h j b x)
      (sourceCouplingEnergy n k p d h j b) 1|) 1) _ at htherm
  simp only [zero_mul,add_zero] at htherm
  have hC := hc.2.2.1
  simp only [sourceCouplingThermal,zero_mul,add_zero] at hC
  have hD := hc.2.2.2
  simp only [sourceCouplingMean,zero_mul,add_zero] at hD
  have hr := kernel_scaled_energy_concentration (sourceFullSpinLeafKernel n k)
    ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (sourceCouplingHamiltonian_measurable n k f p d h u) (sourceCouplingEnergy_measurable n k p d h j)
    (sourceCoupling_all_exp_ae n k f p d h hh0 hh u j z t)
    (show 0<(1/(n+1:ℕ):ℝ) by positivity) hmean htherm hC hD
  exact hr

end SphericalPerceptronFreeEnergy

end

end OAI
