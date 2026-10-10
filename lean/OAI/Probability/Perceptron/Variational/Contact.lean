import Mathlib
import OAI.Probability.Perceptron.Variational.CouplingKernel

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

abbrev sourceFullSpinLeafKernel (n k : ℕ) : Kernel (SourceBaseData n k × (ℕ → ℝ))
    (NormalizedSpin (n+1) × IndexedLeaf k) :=
  (sourceSpinLeafKernel n k).comap Prod.fst measurable_fst

def sourceCouplingMean (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (r : ℝ)
    (a : SourceBaseData n k × (ℕ → ℝ)) : ℝ :=
  (1/(n+1:ℕ))*tiltMean (sourceSpinLeafKernel n k a.1)
    (fun x => sourceCouplingHamiltonian n k f p d h u a x+r*sourceCouplingEnergy n k p d h j a x)
    (sourceCouplingEnergy n k p d h j a) 1

def sourceCouplingThermal (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (r : ℝ)
    (a : SourceBaseData n k × (ℕ → ℝ)) : ℝ :=
  let H := fun x => sourceCouplingHamiltonian n k f p d h u a x+r*sourceCouplingEnergy n k p d h j a x
  let Y := sourceCouplingEnergy n k p d h j a
  Real.sqrt (1/(n+1:ℕ))*tiltMean (sourceSpinLeafKernel n k a.1) H
    (fun x => |Y x-tiltMean (sourceSpinLeafKernel n k a.1) H Y 1|) 1

def sourceCouplingVariance (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (r : ℝ)
    (a : SourceBaseData n k × (ℕ → ℝ)) : ℝ :=
  let H := fun x => sourceCouplingHamiltonian n k f p d h u a x+r*sourceCouplingEnergy n k p d h j a x
  let Y := sourceCouplingEnergy n k p d h j a
  (1/(n+1:ℕ))*tiltMean (sourceSpinLeafKernel n k a.1) H
    (fun x => (Y x-tiltMean (sourceSpinLeafKernel n k a.1) H Y 1)^2) 1

lemma sourceCoupling_observables_measurable (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (r : ℝ) :
    Measurable (sourceCouplingMean n k f p d h u j r) ∧
      Measurable (sourceCouplingThermal n k f p d h u j r) ∧
      Measurable (sourceCouplingVariance n k f p d h u j r) := by
  have hY := sourceCouplingEnergy_measurable n k p d h j
  have hH : Measurable (Function.uncurry (fun a x =>
      sourceCouplingHamiltonian n k f p d h u a x+r*sourceCouplingEnergy n k p d h j a x)) :=
    (sourceCouplingHamiltonian_measurable n k f p d h u).add (hY.const_mul r)
  exact ⟨(kernel_tiltMean_measurable (sourceFullSpinLeafKernel n k) hH hY).const_mul _,
    (kernel_tiltCenteredAbs_measurable (sourceFullSpinLeafKernel n k) hH hY).const_mul _,
    (kernel_tiltCenteredVariance_measurable (sourceFullSpinLeafKernel n k) hH hY).const_mul _⟩

lemma sourceCoupling_thermal_bound_ae (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (z : Fin k → ℝ) (t : ℝ≥0) (r : ℝ) :
    ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw,
      0 ≤ sourceCouplingThermal n k f p d h u j r a ∧
        (sourceCouplingThermal n k f p d h u j r a)^2 ≤ sourceCouplingVariance n k f p d h u j r a := by
  filter_upwards [sourceCoupling_all_exp_ae n k f p d h hh0 hh u j z t] with a ha
  have hH : Measurable (sourceCouplingHamiltonian n k f p d h u a) :=
    sourceCouplingHamiltonian_section n k f p d h u a
  have hY : Measurable (sourceCouplingEnergy n k p d h j a) :=
    sourceCouplingEnergy_section n k p d h j a
  constructor
  · exact mul_nonneg (Real.sqrt_nonneg _) (tiltMean_nonneg _ (fun _ => abs_nonneg _) 1)
  · unfold sourceCouplingThermal sourceCouplingVariance
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    exact mul_le_mul_of_nonneg_left (coupling_thermal_abs_sq_le _ hH hY ha r) (by positivity)

lemma source_contact_thermal_disorder (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
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
    let D := sourceCouplingMean n k f p d h u j 0
    let U := sourceCouplingThermal n k f p d h u j 0
    MemLp U 2 P ∧ Integrable D P ∧ (∫ b, U b ∂P) ≤ Real.sqrt (2*c) ∧
      (∫ b, |D b-∫ b', D b' ∂P| ∂P) ≤
        c*s+4*Real.sqrt (enrichedVarianceConstant k z f H T/(n+1:ℕ))/s := by
  let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
  have hreg := sourceCoupling_regular_ae n k f p d h hh0 hh u j z t
  have htherm := sourceCoupling_thermal_bound_ae n k f p d h hh0 hh u j z t 0
  have hmeas := sourceCoupling_observables_measurable n k f p d h u j
  apply quadratic_contact_thermal_disorder_separate P
    (F := fun r => sourceKernelPressure n k f p d (u+Pi.single j r) h)
    (D := sourceCouplingMean n k f p d h u j)
    (u := 0) (a := a) (c := c) (s := s)
    (V := enrichedVarianceConstant k z f H T/(n+1:ℕ))
    (J := sourceCouplingVariance n k f p d h u j 0) (U := sourceCouplingThermal n k f p d h u j 0)
  · intro r
    have hr := sourceKernelPressure_memLp n k f p d (u+Pi.single j r) h z hz hz0 hz1 t
    exact hr
  · exact fun r => (hmeas r).1.aestronglyMeasurable
  · exact (hmeas 0).2.2.aestronglyMeasurable
  · exact (hmeas 0).2.1.aestronglyMeasurable
  · exact htherm.mono fun _ h => h.1
  · exact htherm.mono fun _ h => h.2
  · exact hreg.mono fun _ h => ⟨h.1,h.2.1,h.2.2.1⟩
  · exact hs
  · exact hreg.mono fun _ h => h.2.2.2 0
  · exact hmin
  · simpa only [zero_add,Pi.single_zero,add_zero] using hp
  · simpa only [zero_sub,Pi.single_zero,add_zero] using hm
  · have hv := sourceKernelPressure_variance n k f p d (u+Pi.single j s) h z hz hz0 hz1 hup hH hhH t ht
    simpa only [zero_add] using hv
  · have hv := sourceKernelPressure_variance n k f p d u h z hz hz0 hz1 hu hH hhH t ht
    simpa only [Pi.single_zero,add_zero] using hv
  · have hv := sourceKernelPressure_variance n k f p d (u+Pi.single j (-s)) h z hz hz0 hz1 hum hH hhH t ht
    simpa only [zero_sub] using hv

end SphericalPerceptronFreeEnergy
end

end OAI
