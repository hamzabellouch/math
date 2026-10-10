import OAI.Geometry.CylinderCovering.Rational.ConstructionDefinitions
import OAI.Geometry.CylinderCovering.Rational.Realization
import OAI.Geometry.CylinderCovering.Rational.Domain

namespace OAI

open Set MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section

namespace SlopeRational

theorem rational_approximation_eligibility {d ε : ℝ} (hd : 0 < d)
    (hε : 0 < ε) (hsmall : ε < 8 * d) (q : ℝ) :
    IsCompact (labelDomain d ε q) ∧
    volume (frontier (labelDomain d ε q)) = 0 ∧
    RuledApproximation.SmoothNear ∞ (labelDomain d ε q) (field d) ∧
    (∀ p ∈ labelDomain d ε q,
      RuledApproximation.HyperbolicAt (1 / 2) (fun z => ε • field d z) p) ∧
    (∀ p ∈ labelDomain d ε q,
      RuledApproximation.HyperbolicAt (1 / 2) (fun z => -ε • field d z) p) := by
  refine ⟨labelDomain_isCompact d ε q, volume_frontier_labelDomain d ε q,
    field_smoothNear_labelDomain hd ε q, ?_, ?_⟩
  · intro p hp
    exact rational_hyperbolic hd hε.ne' (by simpa [abs_of_pos hε] using hsmall) hp
  · intro p hp
    exact rational_hyperbolic hd (neg_ne_zero.mpr hε.ne')
      (by simpa [abs_of_pos hε] using hsmall) hp

theorem approximationEligibility : ApproximationEligibilityStatement := by
  intro d hd q _hq
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 8 * d :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 8 * d by positivity))
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hs
  exact rational_approximation_eligibility hd hε hs (q ε)

end SlopeRational

end

end OAI
