import OAI.Combinatorics.Progressions.Probability.CoefficientDensityAverage

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem coefficientAverage_density_l1 {W R X Y : Type*}
    [MeasurableSpace W] [MeasurableSpace R] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure W) (ρ : Measure R) (ν : Measure X) (ξ : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] [SFinite ξ]
    (D : R → Y → ℝ) (hD : Measurable (Function.uncurry D))
    (hprob : ∀ r, (∀ y, 0 ≤ D r y) ∧ Integrable (D r) ξ ∧ (∫ y, D r y ∂ξ) = 1)
    (g : W × Y → ℝ) (hg : Measurable g) (hgi : Integrable g (μ.prod ξ))
    (U : (W × R) × X → W × Y)
    (hlaw : ∀ φ : W × Y → ℝ, Measurable φ → (∀ p, ‖φ p‖ ≤ 1) →
      (∫ p, φ (U p) ∂(μ.prod ρ).prod ν) = ∫ p, g p*φ p ∂μ.prod ξ)
    {ε : ℝ}
    (hcomp : ∀ φ : W × Y → ℝ, Measurable φ → (∀ p, ‖φ p‖ ≤ 1) →
      |(∫ p : (W × R) × Y, D p.1.2 p.2*φ (p.1.1, p.2) ∂(μ.prod ρ).prod ξ) -
        ∫ p, φ (U p) ∂(μ.prod ρ).prod ν| ≤ ε) :
    (∫ p : W × Y, |densityMixture ρ D p.2-g p| ∂μ.prod ξ) ≤ ε := by
  have hm : Measurable (densityMixture ρ D) := hD.stronglyMeasurable.integral_prod_left'.measurable
  have hp := densityMixture_probability_density ρ ξ D hD (Filter.Eventually.of_forall hprob)
  apply density_l1_le_of_bounded_tests (μ.prod ξ) (fun p => densityMixture ρ D p.2) g
    (hm.comp measurable_snd) hg (hp.2.1.comp_snd μ) hgi
  intro φ hφ hbound
  have he := hcomp φ hφ hbound
  rw [retained_coefficient_density_average μ ρ ξ D hD hprob φ hφ hbound,
    hlaw φ hφ hbound] at he
  exact he

end Erdos3

end

end OAI
