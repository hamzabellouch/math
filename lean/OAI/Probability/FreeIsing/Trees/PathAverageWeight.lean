import OAI.Probability.FreeIsing.Estimates.BoundedAverageConcentration
import OAI.Probability.FreeIsing.Estimates.DependentWeight

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367
namespace PathAverageWeight

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integral_mul_le_of_independent_average
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty) {τ C M : ℝ}
    (hτ : 0 ≤ τ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (h_mean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) ≤ τ / 2)
    {z g : Ω → ℝ} (hz : Integrable z μ) (hg : Measurable g)
    (hz_nonneg : ∀ᵐ x ∂μ, 0 ≤ z x) (hz_bound : ∀ᵐ x ∂μ, z x ≤ M)
    (hg_nonneg : ∀ᵐ x ∂μ, 0 ≤ g x) (hg_bound : ∀ᵐ x ∂μ, g x ≤ 1)
    (hdom : ∀ᵐ x ∂μ, g x ≤ C * ((∑ i ∈ s, X i x) / (s.card : ℝ))) :
    (∫ x, z x * g x ∂μ) ≤
      (C * τ) * (∫ x, z x ∂μ) + M * Real.exp (-(s.card : ℝ) * τ ^ 2 / 2) := by
  exact DependentWeight.integral_mul_le_of_dominated_tail hz hg hC hτ hM
    hz_nonneg hz_bound hg_nonneg hg_bound hdom
    (BoundedAverageConcentration.measureReal_average_ge_le h_indep s hs hτ
      h_meas h_bdd h_mean)

theorem integral_mul_le_double_exp
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty) {b ℓ q C M : ℝ}
    (hb : 0 < b) (hℓ : 0 ≤ ℓ) (hq : q ≤ Real.log b / 8)
    (hcard : b ^ (ℓ / 2 - 1) ≤ (s.card : ℝ))
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (h_mean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) ≤ Real.exp (-q * ℓ) / 2)
    {z g : Ω → ℝ} (hz : Integrable z μ) (hg : Measurable g)
    (hz_nonneg : ∀ᵐ x ∂μ, 0 ≤ z x) (hz_bound : ∀ᵐ x ∂μ, z x ≤ M)
    (hg_nonneg : ∀ᵐ x ∂μ, 0 ≤ g x) (hg_bound : ∀ᵐ x ∂μ, g x ≤ 1)
    (hdom : ∀ᵐ x ∂μ, g x ≤ C * ((∑ i ∈ s, X i x) / (s.card : ℝ))) :
    (∫ x, z x * g x ∂μ) ≤
      (C * Real.exp (-q * ℓ)) * (∫ x, z x ∂μ) +
        M * Real.exp (-(b ^ (ℓ / 4)) / (2 * b)) := by
  exact DependentWeight.integral_mul_le_of_dominated_tail hz hg hC (Real.exp_pos _).le hM
    hz_nonneg hz_bound hg_nonneg hg_bound hdom
    (BoundedAverageConcentration.measureReal_average_ge_le_double_exp
      h_indep s hs hb hℓ hq hcard h_meas h_bdd h_mean)

theorem integral_mul_le_of_kernel_average
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y Ω) [IsMarkovKernel κ]
    {X : ι → Ω → ℝ} (s : Finset ι) (hs : s.Nonempty) {τ C M : ℝ}
    (hτ : 0 ≤ τ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (h_meas : ∀ i ∈ s, Measurable (X i))
    (h_indep : ∀ᵐ y ∂ν, iIndepFun X (κ y))
    (h_bdd : ∀ᵐ y ∂ν, ∀ i ∈ s, ∀ᵐ ω ∂κ y, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (h_mean : ∀ᵐ y ∂ν, ∀ i ∈ s, (∫ ω, X i ω ∂κ y) ≤ τ / 2)
    {z g : Ω → ℝ} (hz : Integrable z (κ ∘ₘ ν)) (hg : Measurable g)
    (hz_nonneg : ∀ᵐ x ∂κ ∘ₘ ν, 0 ≤ z x) (hz_bound : ∀ᵐ x ∂κ ∘ₘ ν, z x ≤ M)
    (hg_nonneg : ∀ᵐ x ∂κ ∘ₘ ν, 0 ≤ g x) (hg_bound : ∀ᵐ x ∂κ ∘ₘ ν, g x ≤ 1)
    (hdom : ∀ᵐ x ∂κ ∘ₘ ν, g x ≤ C * ((∑ i ∈ s, X i x) / (s.card : ℝ))) :
    (∫ x, z x * g x ∂κ ∘ₘ ν) ≤
      (C * τ) * (∫ x, z x ∂κ ∘ₘ ν) + M * Real.exp (-(s.card : ℝ) * τ ^ 2 / 2) := by
  apply DependentWeight.integral_mul_le_of_dominated_tail hz hg hC hτ hM
    hz_nonneg hz_bound hg_nonneg hg_bound hdom
  have hp := BoundedAverageConcentration.measure_average_ge_le_of_kernel
    ν κ s hs hτ h_meas h_indep h_bdd h_mean
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
  simpa only [measureReal_def, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hr

end PathAverageWeight
end Problem367

end

end OAI
