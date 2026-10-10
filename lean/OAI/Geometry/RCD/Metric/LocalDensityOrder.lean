import OAI.Geometry.RCD.Metric.LocalSignedMeasureOrder
import OAI.Geometry.RCD.Metric.SignedSourceDensity
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

namespace OAI

/-! # Compact Lipschitz tests detect the sign of a local integrable density -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] (μ : Measure X)

theorem local_density_nonneg_of_tests {f : X → ℝ} (hf : Integrable f μ)
    {Ω S : Set X} (hS : MeasurableSet S)
    (χ : X →ᵇ ℝ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : 0 ≤ χ) (hχ1 : ∀ x ∈ S, χ x = 1)
    (htest : ∀ q : compactLipschitzTests Ω, 0 ≤ (q : X →ᵇ ℝ) →
      0 ≤ ∫ x, (q : X →ᵇ ℝ) x*f x ∂μ) :
    ∀ᵐ x ∂μ.restrict S, 0 ≤ f x := by
  have hp : 0 ≤ (μ.withDensityᵥ f).restrict S := by
    apply signedMeasure_nonneg_restrict_of_tests _ hS χ hχ hχc hχΩ hχ0 hχ1
    intro q hq
    rw [integral_signedDensity μ hf]
    exact htest q hq
  apply ae_nonneg_of_forall_setIntegral_nonneg hf.integrableOn
  intro t ht _
  have hn := hp t ht
  rw [VectorMeasure.restrict_apply (μ.withDensityᵥ f) hS ht,withDensityᵥ_apply hf (ht.inter hS)] at hn
  simpa only [zero_apply,Measure.restrict_restrict ht] using hn


theorem local_density_nonneg_of_tests_integrableOn {f : X → ℝ} {Ω S : Set X}
    (hΩ : MeasurableSet Ω) (hf : IntegrableOn f Ω μ) (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    (χ : X →ᵇ ℝ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : 0 ≤ χ) (hχ1 : ∀ x ∈ S, χ x = 1)
    (htest : ∀ q : compactLipschitzTests Ω, 0 ≤ (q : X →ᵇ ℝ) →
      0 ≤ ∫ x, (q : X →ᵇ ℝ) x*f x ∂μ) :
    ∀ᵐ x ∂μ.restrict S, 0 ≤ f x := by
  have hi : Integrable (Ω.indicator f) μ := (integrable_indicator_iff hΩ).mpr hf
  have hpos := local_density_nonneg_of_tests μ hi hS χ hχ hχc hχΩ hχ0 hχ1
    (fun q hq => by
      have he : (fun x => (q : X →ᵇ ℝ) x*Ω.indicator f x) =
          (fun x => (q : X →ᵇ ℝ) x*f x) := by
        funext x
        by_cases hx : x ∈ Ω
        · rw [indicator_of_mem hx]
        · have hz : (q : X →ᵇ ℝ) x = 0 := image_eq_zero_of_notMem_tsupport
            (fun hs => hx (q.property.choose_spec.2.2 hs))
          rw [hz,zero_mul,zero_mul]
      rw [he]
      exact htest q hq)
  filter_upwards [hpos,ae_restrict_mem hS] with x hx hxs
  simpa only [indicator_of_mem (hSΩ hxs)] using hx

end RegularPointCoordinates

end

end OAI
