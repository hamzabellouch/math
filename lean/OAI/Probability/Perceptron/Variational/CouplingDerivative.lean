import Mathlib
import OAI.Probability.Perceptron.Variational.EnergyMean
import OAI.Probability.Perceptron.Variational.GaussianAbsoluteEnergyBound

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceExpectedPressure_coordinate_derivative (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (u : Fin (n+1) → ℝ)
    (j : Fin (n+1)) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
    ∃ D : ℝ,
      HasDerivAt (fun r => ∫ a, sourceKernelPressure n k f p d (u+Pi.single j r) h a ∂P) D 0 ∧
      D = (1/(n+1:ℕ))*(perturbationAmplitude (n+1) (fun _ => 1) j*perturbationAmplitude (n+1) u j*
        ((k:ℝ)/(k+1:ℕ))^(d j)-
        ∫ a, gibbsReplicaMean (sourceSpinLeafKernel n k a.1)
          (sourceCouplingHamiltonian n k f p d h u a) 2
          (fun x => sourceCouplingCovariance n k p d u j (x 1) (x 0)) ∂P) := by
  dsimp only
  let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
  have hi (r : ℝ) : Integrable (sourceKernelPressure n k f p d (u+Pi.single j r) h) P := by
    have hr := sourceKernelPressure_memLp n k f p d (u+Pi.single j r) h z hz hz0 hz1 t
    exact hr.integrable (by norm_num)
  have hreg := sourceCoupling_regular_ae n k f p d h hh0 hh u j z t
  have hd := annealed_convex_hasDerivAt P (D := sourceCouplingMean n k f p d h u j)
    (fun r => (hi r).aestronglyMeasurable)
    (fun r => (sourceCoupling_observables_measurable n k f p d h u j r).1.aestronglyMeasurable)
    hi (hreg.mono fun a ha => ⟨ha.2.1,ha.2.2.1⟩) 0
  refine ⟨_,hd.2,?_⟩
  simp only [sourceCouplingMean,zero_mul,add_zero,integral_const_mul]
  rw [sourceCoupling_energy_mean n k f p d h hh0 hh u j z t
    (sourceCoupling_abs_energy_integrable n k f p d h hh0 hh u j z t)]

lemma sourceExpectedPressure_coordinate_derivative_bound (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (u : Fin (n+1) → ℝ)
    (j : Fin (n+1)) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    ∃ D : ℝ,
      HasDerivAt (fun r => ∫ a, sourceKernelPressure n k f p d (u+Pi.single j r) h a
        ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw)) D 0 ∧
      |D| ≤ 2*|perturbationAmplitude (n+1) (fun _ => 1) j*perturbationAmplitude (n+1) u j|/(n+1:ℕ) := by
  obtain ⟨D,hD,rfl⟩ := sourceExpectedPressure_coordinate_derivative n k f p d h hh0 hh u j z hz hz0 hz1 t
  refine ⟨_,hD,?_⟩
  let C := |perturbationAmplitude (n+1) (fun _ => 1) j*perturbationAmplitude (n+1) u j|
  have hcov (a : SourceBaseData n k × (ℕ → ℝ)) :
      |gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (sourceCouplingHamiltonian n k f p d h u a) 2
        (fun x => sourceCouplingCovariance n k p d u j (x 1) (x 0))| ≤ C :=
    tiltMean_bound_general _ (replicaPotential_measurable (sourceCouplingHamiltonian_section n k f p d h u a) 2)
      (sourceCouplingCovariance_measurable n k 2 p d u j 1 0)
      (abs_nonneg _) (fun x => sourceCouplingCovariance_bound n k p d u j _ _)
  have hci : |∫ a, gibbsReplicaMean (sourceSpinLeafKernel n k a.1)
      (sourceCouplingHamiltonian n k f p d h u a) 2
      (fun x => sourceCouplingCovariance n k p d u j (x 1) (x 0))
      ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw)| ≤ C := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := ((sourceBaseDataLaw n k z t).prod countableGaussianLaw))
      (f := fun a => gibbsReplicaMean (sourceSpinLeafKernel n k a.1) (sourceCouplingHamiltonian n k f p d h u a) 2
        (fun x => sourceCouplingCovariance n k p d u j (x 1) (x 0)))
      (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using hcov a)
  have hk : |((k:ℝ)/(k+1:ℕ))^(d j)| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg (by positivity) _)]
    apply pow_le_one₀ (by positivity)
    apply (div_le_one₀ (by positivity : (0:ℝ)<(k+1:ℕ))).mpr
    exact_mod_cast Nat.le_succ k
  have hdiag : |perturbationAmplitude (n+1) (fun _ => 1) j*perturbationAmplitude (n+1) u j*
      ((k:ℝ)/(k+1:ℕ))^(d j)| ≤ C := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hk (abs_nonneg _)).trans_eq (mul_one _)
  have hsum := (abs_sub _ _).trans (add_le_add hdiag hci)
  rw [abs_mul,abs_of_pos (by positivity : (0:ℝ)<1/(n+1:ℕ))]
  calc
    _ ≤ (1/(n+1:ℕ))*(C+C) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp [C]; ring

end SphericalPerceptronFreeEnergy
end

end OAI
