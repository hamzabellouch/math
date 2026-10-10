import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! # Closed increment constraints pass to one-sided derivatives -/

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

/-- Only positive short segments are needed to constrain the derivative.
The derivative limit itself supplies all required convergence. -/
theorem derivative_mem_of_short_increments
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : ℝ → W) (w : W) (hderiv : HasDerivAt f w 0)
    (S : Set W) (hS : IsClosed S) {T₀ : ℝ} (hT₀ : 0 < T₀)
    (hinc : ∀ t : ℝ, 0 < t → t < T₀ → t⁻¹ • (f t - f 0) ∈ S) : w ∈ S := by
  apply hS.mem_of_tendsto hderiv.tendsto_slope_zero_right
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < T₀ :=
    (eventually_lt_nhds hT₀).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, hsmall] with t ht htT
  simpa only [zero_add] using hinc t ht htT

end PolycyclicRecognition

end OAI
