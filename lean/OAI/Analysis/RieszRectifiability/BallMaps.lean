import OAI.Analysis.RieszRectifiability.PerMeasure

namespace OAI

/-!
# The per-measure ball-map conclusion

The higher-codimension rectifiability theorem is restated with its conclusion
expanded: one positive mass fraction and one Lipschitz bound work at every
support point and admissible radius of the given measure. The lower bound is
for the actual image of a map from a Euclidean ball, intersected with the ambient
support ball. The hypotheses and admissible-radius condition are unchanged.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

/-- The per-measure rectifiability theorem with its ball-map conclusion expanded. -/
theorem exact_unfolded_ball_map_conclusion (d n : ℕ) (hd : 4 ≤ d) (hn : 2 ≤ n) (hnd : n + 2 ≤ d)
    (μ : Measure (Ambient d)) (hreg : μ.Regular) (hAD : ADRegular n μ) (hRiesz : RieszL2Bounded n μ) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ M : ℝ≥0,
      ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ∃ g : ball (0 : Ambient n) r → Ambient d,
          LipschitzWith M g ∧ ENNReal.ofReal (θ * r ^ n) ≤ μ (ball x r ∩ Set.range g) :=
  exact_higher_codimension_riesz_rectifiability d n hd hn hnd μ hreg hAD hRiesz

end

end RieszRectifiability

end OAI
