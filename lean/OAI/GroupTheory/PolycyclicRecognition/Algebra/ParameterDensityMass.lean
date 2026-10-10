import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubexponentialBounds
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-! # Density bounds retain subexponential parameter volume -/

namespace PolycyclicRecognition

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

/-- The density bound is imposed before restriction to the successful set. -/
theorem measure_le_of_density_bound {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : Measure A) (f : A → ℝ≥0∞) (hν : ν = μ.withDensity f)
    {D : ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≤ D) : ν ≤ D • μ := by
  rw [hν, ← withDensity_const]
  exact withDensity_mono hf

/-- A subexponential density upper bound turns positive successful probability
into the volume lower bound used by the polynomial image argument. -/
theorem subexponential_volume_of_probability
    {A : Type*} [MeasurableSpace A]
    (μ ν : ℝ → Measure A) (E : ℝ → Set A) (D : ℝ → ℝ≥0)
    (hfinite : ∀ r, μ r (E r) ≠ ∞)
    (hdom : ∀ r, ν r ≤ (D r : ℝ≥0∞) • μ r)
    (hprob : HasSubexponentialLowerBound (fun r => (ν r (E r)).toReal))
    (hD : HasSubexponentialUpperBound (fun r => (D r : ℝ)))
    (hpos : ∀ᶠ r in atTop, 0 < D r) :
    HasSubexponentialLowerBound (fun r => (μ r (E r)).toReal) := by
  have hdiv := hprob.div hD hpos
  apply hdiv.mono
  filter_upwards [hpos] with r hr
  apply (div_le_iff₀ (show 0 < (D r : ℝ) from hr)).mpr
  have hbound := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (hfinite r)) (hdom r (E r))
  simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, mul_comm] using hbound

end PolycyclicRecognition

end OAI
