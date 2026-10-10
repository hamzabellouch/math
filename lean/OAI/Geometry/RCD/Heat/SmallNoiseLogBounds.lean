import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

namespace OAI

/-! # Vanishing scaled logarithms of uniformly positive bounded masses -/

open Set Filter
open scoped Topology
namespace RegularPointCoordinates

theorem small_noise_log_tendsto_zero {ε f : ℕ → ℝ} {c C : ℝ}
    (hε : ∀ k, 0 ≤ ε k) (hε0 : Tendsto ε atTop (𝓝 0)) (hc : 0 < c)
    (hbound : ∀ᶠ k in atTop, c ≤ f k ∧ f k ≤ C) :
    Tendsto (fun k => ε k*Real.log (f k)) atTop (𝓝 0) := by
  have hl := hε0.mul_const (Real.log c)
  have hu := hε0.mul_const (Real.log C)
  simp only [zero_mul] at hl hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [hbound] with k hk
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hc hk.1) (hε k)
  · filter_upwards [hbound] with k hk
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (hc.trans_le hk.1) hk.2) (hε k)

end RegularPointCoordinates

end OAI
