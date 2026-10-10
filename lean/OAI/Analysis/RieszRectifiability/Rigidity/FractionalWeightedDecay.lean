import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSpatialDecay
import OAI.Analysis.RieszRectifiability.Kernel.PolynomialDecayBounds
import OAI.Analysis.RieszRectifiability.Limits.SchwartzMomentContinuity

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology

def fractionalSchwartzUniformSize (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) : ℝ :=
  let C := ((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal
  4 * (C * 2 ^ (p + 1) * 2 ^ p) * SchwartzMap.seminorm ℝ 0 2 g +
    8 * (C * 2 ^ (p + 1)) * SchwartzMap.seminorm ℝ 0 0 g

def fractionalSchwartzWeightedSize (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) : ℝ :=
  2 ^ (p + 3) * (fractionalSchwartzUniformSize p g + fractionalSchwartzDecaySize p g)

theorem fractionalSchwartzWeightedSize_nonneg (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) :
    0 ≤ fractionalSchwartzWeightedSize p g := by
  have hD := fractionalSchwartzDecaySize_nonneg p g
  have hU : 0 ≤ fractionalSchwartzUniformSize p g := by
    unfold fractionalSchwartzUniformSize
    positivity
  unfold fractionalSchwartzWeightedSize
  positivity

theorem fractionalSchwartzTest_polynomial_decay (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (hmean : (∫ y, g y) = 0) (x : Ambient (p + 1)) :
    ‖fractionalSchwartzTest p g x‖ ≤
      fractionalSchwartzWeightedSize p g * polynomialDecay (p + 3) x := by
  apply polynomial_decay_from_uniform_and_far_bound (p + 3) (fractionalSchwartzTest p g)
    (fractionalSchwartzUniformSize p g) (fractionalSchwartzDecaySize p g)
  · unfold fractionalSchwartzUniformSize
    positivity
  · exact fractionalSchwartzDecaySize_nonneg p g
  · exact fractionalSchwartzTest_uniform_bound p g
  · exact fractionalSchwartzTest_spatial_decay p g hmean

theorem fractionalSchwartzWeightedSize_tendsto_zero (p : ℕ)
    (G : ℕ → 𝓢(Ambient (p + 1), ℂ)) (ht : Tendsto G atTop (𝓝 0)) :
    Tendsto (fun j => fractionalSchwartzWeightedSize p (G j)) atTop (𝓝 0) := by
  let C := ((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal
  have hsem := schwartz_seminorm_tendsto_zero G ht
  have hmoment := schwartz_first_absolute_moment_tendsto_zero G ht
  have hU : Tendsto (fun j => fractionalSchwartzUniformSize p (G j)) atTop (𝓝 0) := by
    simpa only [fractionalSchwartzUniformSize, C, mul_zero, add_zero] using!
      ((hsem 0 2).const_mul (4 * (C * 2 ^ (p + 1) * 2 ^ p))).add
        ((hsem 0 0).const_mul (8 * (C * 2 ^ (p + 1))))
  have hD : Tendsto (fun j => fractionalSchwartzDecaySize p (G j)) atTop (𝓝 0) := by
    simpa only [fractionalSchwartzDecaySize, C, mul_zero, add_zero] using!
      ((hsem (p + 4) 2).const_mul (4 * (C * 2 ^ (p + 1) * 2 ^ p) * 2 ^ (p + 3))).add
        (((hsem (p + 2) 0).const_mul (4 * C * 2 ^ (p + 1))).add
          (hmoment.const_mul (((p + 1 : ℝ) + 1) * 2 ^ (p + 3) + 2 ^ (p + 4) + 2)))
  simpa only [fractionalSchwartzWeightedSize, add_zero, mul_zero] using!
    (hU.add hD).const_mul ((2 : ℝ) ^ (p + 3))

end

end RieszRectifiability

end OAI
