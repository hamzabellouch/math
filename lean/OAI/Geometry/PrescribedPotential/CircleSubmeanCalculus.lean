import Mathlib

namespace OAI

/-! Circle Submean Calculus. -/

section

 

noncomputable section
open Set Filter Topology Metric MeasureTheory
namespace PotentialABP

lemma hasDerivAt_intervalIntegral_continuous
    {F F' : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hderiv : ∀ r θ, HasDerivAt (fun s => F s θ) (F' r θ) r)
    (a b r : ℝ) :
    HasDerivAt (fun s => ∫ θ in a..b, F s θ) (∫ θ in a..b, F' r θ) r := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall r 1).prod isCompact_uIcc).bddAbove_image
    hF'.norm.continuousOn
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ => C) (s := ball r 1) (ball_mem_nhds r (by norm_num)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [] with s
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with θ hθ s hs
    exact hC ⟨(s,θ), ⟨ball_subset_closedBall hs, uIoc_subset_uIcc hθ⟩, rfl⟩
  · exact intervalIntegrable_const
  · filter_upwards [] with θ _ s _
    exact hderiv s θ

end PotentialABP

end
end

end OAI
