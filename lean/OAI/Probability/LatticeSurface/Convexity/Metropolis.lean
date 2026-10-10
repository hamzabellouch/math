import Mathlib
import OAI.Probability.LatticeSurface.Convexity.MetropolisSupport

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set ConvexSkorokhod

theorem weighted_metropolis_pair (m : ℕ)
    (B : Body (FreeHeightSpace m)) (c : FreeHeightSpace m) (r R : ℝ)
    (hr : 0<r) (hball : Metric.closedBall c r⊆B.carrier)
    (hR : ∀z∈B.carrier,‖z-c‖≤R) (b v : FreeHeightSpace m) :
    IsProbabilityMeasure (metropolisShiftPair (weightedBodyLaw B b) v) ∧
    (metropolisShiftPair (weightedBodyLaw B b) v).map Prod.fst=weightedBodyLaw B b ∧
    (metropolisShiftPair (weightedBodyLaw B b) v).map Prod.snd=weightedBodyLaw B b ∧
    (metropolisShiftPair (weightedBodyLaw B b) v).map Prod.swap=
      metropolisShiftPair (weightedBodyLaw B b) v := by
  let := weightedBodyLaw_probability B c r R hr hball hR b
  exact ⟨metropolisShiftPair_probability _ _, metropolisShiftPair_fst _ _,
    metropolisShiftPair_snd _ _, metropolisShiftPair_swap _ _⟩

end BrownianForcing

end OAI
