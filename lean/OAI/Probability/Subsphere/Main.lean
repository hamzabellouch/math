import Mathlib
import OAI.Probability.Subsphere.Estimates.Weighted
import OAI.Probability.Subsphere.Estimates.HalfPrecision
import OAI.Probability.Subsphere.Estimates.AffinePrecision
import OAI.Probability.Subsphere.Estimates.FixedPrecision
import OAI.Probability.Subsphere.Mixture.Domination

namespace OAI

section
noncomputable section
universe u v w
namespace SubsphereCurrent

theorem full_current_main_scope : CurrentMainScope.{u,v,w} := by
  exact ⟨explicit_precision, Weighted.radius_weighted_full_estimate,
    half_precision, Affine.all_affine_full_estimate, Fixed.dimension_estimate,
    Mixture.mixture_estimate⟩

end SubsphereCurrent
end
end

end OAI
