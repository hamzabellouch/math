import Mathlib
import OAI.Probability.SphericalField.Positivity.JointLaw
import OAI.Probability.SphericalField.Entropy.Quantile
import OAI.Probability.SphericalField.Perceptron.Concentration
import OAI.Probability.SphericalField.Positivity.FiniteLaws
import OAI.Probability.SphericalField.Gaussian.Poincare
import OAI.Probability.SphericalField.Gibbs.MixedVariance
import OAI.Probability.SphericalField.Gibbs.Contact
import OAI.Probability.SphericalField.Gibbs.GaussianIdentities
import OAI.Probability.SphericalField.Sphere.Rotations
import OAI.Probability.SphericalField.Gibbs.LimitLaws
import OAI.Probability.SphericalField.Control.SmoothTerminals
import OAI.Probability.SphericalField.Heat.Continuity
import OAI.Probability.SphericalField.Fields.BoundedUniform
import OAI.Probability.SphericalField.Quantiles.AlmostEverywhere

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

theorem spherical_linear_field_formula : SphericalLinearFieldFormula := by
  constructor
  · intro k w hw hw1
    constructor
    · intro h hh hh0
      obtain ⟨q,hq,hq1,hmin,-⟩ := finiteSphericalFieldValue_pointwise_dual w h hw hw1 hh hh0
      exact ⟨q,hq,hq1,hmin⟩
    · intro K hK hf
      exact finiteSphericalFieldValue_compact_uniform w hw hw1 hK hf
  · intro B hB0 hB1 ε hε
    filter_upwards [boundedSphericalFieldValue_stationary_uniform B hB0 hB1 ε hε] with n hn q hq hb
    refine ⟨entropy_quantileTrial_finite_of_ae_bounded q hq hB0 hB1 hb,?_,?_⟩
    · filter_upwards [stationaryQuantileField_ae_eq q hq hB0 hB1 hb] with u hu
      rw [hu]
      ring
    · have h := hn (clippedQuantile q hq B hB0)
      rw [quantileTrial_congr (clippedQuantile_ae_eq q hq hB0 hB1 hb),
        stationaryQuantileField_cross q hq hB0 hB1 hb] at h
      exact h

end SphericalPerceptron
end
end

end OAI
