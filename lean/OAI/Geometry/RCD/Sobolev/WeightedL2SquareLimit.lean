import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Continuous bounded-weight square pairings on L² -/

open Filter MeasureTheory
open scoped NNReal Topology

namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem weightedL2_square_tendsto {v : X → ℝ} (hv : Measurable v) (C : ℝ≥0)
    (hC : ∀ x, |v x| ≤ C) {ds : ℕ → Lp ℝ 2 μ} {d : Lp ℝ 2 μ}
    (hd : Tendsto ds atTop (𝓝 d)) :
    Tendsto (fun k => ∫ x, v x * (ds k x) ^ 2 ∂μ) atTop
      (𝓝 (∫ x, v x * (d x) ^ 2 ∂μ)) := by
  let V := boundedMultiplier μ v hv C hC
  let T := lpMultiplier μ V
  have he (f : Lp ℝ 2 μ) : (∫ x, v x * (f x) ^ 2 ∂μ) = inner ℝ f (T f) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [lpMultiplier_coe μ V f, boundedMultiplier_coe μ v hv C hC] with x hx hV
    change T f x = V x * f x at hx
    change V x = v x at hV
    simp only [Real.inner_apply, hx, hV]
    ring
  simp_rw [he]
  exact hd.inner ((T.continuous.tendsto d).comp hd)

end RegularPointCoordinates

end OAI
