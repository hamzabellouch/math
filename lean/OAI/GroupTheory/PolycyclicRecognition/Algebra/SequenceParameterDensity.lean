import OAI.GroupTheory.PolycyclicRecognition.Algebra.ParameterDensityMass
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponential

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem subexponential_volume_of_probability_sequence
    {A : Type*} [MeasurableSpace A]
    (scale : ℕ → ℝ)
    (μ ν : ℕ → Measure A) (E : ℕ → Set A) (D : ℕ → ℝ≥0)
    (hfinite : ∀ r, μ r (E r) ≠ ∞)
    (hdom : ∀ r, ν r ≤ (D r : ℝ≥0∞) • μ r)
    (hprob : HasSubexponentialLowerBoundSeq scale (fun r => (ν r (E r)).toReal))
    (hD : HasSubexponentialUpperBoundSeq scale (fun r => (D r : ℝ)))
    (hpos : ∀ᶠ r in atTop, 0 < D r) :
    HasSubexponentialLowerBoundSeq scale (fun r => (μ r (E r)).toReal) := by
  have hdiv := hprob.div hD hpos
  apply hdiv.mono
  filter_upwards [hpos] with r hr
  apply (div_le_iff₀ (show 0 < (D r : ℝ) from hr)).mpr
  have hbound := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (hfinite r)) (hdom r (E r))
  simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, mul_comm] using hbound

end PolycyclicRecognition

end

end OAI
