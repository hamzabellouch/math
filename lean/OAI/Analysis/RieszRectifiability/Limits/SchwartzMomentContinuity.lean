import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.SchwartzFirstMomentTails

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Filter Topology

theorem schwartz_first_absolute_moment_seminorm_bound {d : ℕ} (g : 𝓢(Ambient d, ℂ)) :
    (∫ y : Ambient d, ‖y‖ * ‖g y‖) ≤
      2 ^ (volume : Measure (Ambient d)).integrablePower *
        (∫ y : Ambient d, (1 + ‖y‖) ^ (-((volume : Measure (Ambient d)).integrablePower : ℝ))) *
        (SchwartzMap.seminorm ℝ 0 0 g +
          SchwartzMap.seminorm ℝ (1 + (volume : Measure (Ambient d)).integrablePower) 0 g) := by
  simpa only [pow_one, norm_iteratedFDeriv_zero] using!
    SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ (volume : Measure (Ambient d)) g 1 0

theorem schwartz_seminorm_tendsto_zero {d : ℕ} (G : ℕ → 𝓢(Ambient d, ℂ))
    (ht : Tendsto G atTop (𝓝 0)) (k n : ℕ) :
    Tendsto (fun j => SchwartzMap.seminorm ℝ k n (G j)) atTop (𝓝 0) := by
  simpa only [schwartzSeminormFamily_apply, map_zero] using!
    ((schwartz_withSeminorms ℝ (Ambient d) ℂ).continuous_seminorm (k, n)).tendsto 0 |>.comp ht

theorem schwartz_first_absolute_moment_tendsto_zero {d : ℕ}
    (G : ℕ → 𝓢(Ambient d, ℂ)) (ht : Tendsto G atTop (𝓝 0)) :
    Tendsto (fun j => ∫ y : Ambient d, ‖y‖ * ‖G j y‖) atTop (𝓝 0) := by
  let C := 2 ^ (volume : Measure (Ambient d)).integrablePower *
    (∫ y : Ambient d, (1 + ‖y‖) ^ (-((volume : Measure (Ambient d)).integrablePower : ℝ)))
  have h0 := schwartz_seminorm_tendsto_zero G ht 0 0
  have h1 := schwartz_seminorm_tendsto_zero G ht
    (1 + (volume : Measure (Ambient d)).integrablePower) 0
  have hb : Tendsto (fun j => C * (SchwartzMap.seminorm ℝ 0 0 (G j) +
      SchwartzMap.seminorm ℝ (1 + (volume : Measure (Ambient d)).integrablePower) 0 (G j)))
      atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using! (h0.add h1).const_mul C
  exact squeeze_zero (fun j => integral_nonneg fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun j => schwartz_first_absolute_moment_seminorm_bound (G j)) hb

end

end RieszRectifiability

end OAI
