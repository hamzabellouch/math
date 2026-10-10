import OAI.Combinatorics.DiscreteConvexity.WeightedCover
import OAI.Combinatorics.DiscreteConvexity.FourierGlobalBound
import OAI.Combinatorics.DiscreteConvexity.SignedArrays

namespace OAI

/-!
# Small exceptional families at a fixed fraction of the density

The actual biased Fourier weights satisfy both estimates needed by the finite
bin construction.  No monotonicity of the given family is assumed.
-/

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem halfDensity_small {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (F : Family α) (hF : (1 / 2 : ℝ) ≤ familyMeasure q F) :
    Small (q / (2 : ℝ) ^ 70) (exceptional 32 F) := by
  exact weights_small hq0 hq1 (exceptional 32 F) (w q (familyIndicator F))
    (w_nonneg q (familyIndicator F)) (indicator_global_weight_bound q hq0 hq1 F)
    (fun _ hS => exceptional_weight_lower_bound q hF hS)

end TalagrandDiscreteConvexity

end OAI
