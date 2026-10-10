import Mathlib

namespace OAI

/-! # Passing a scalar limit through uniformly close approximations -/

open Filter
open scoped Topology

namespace RegularPointCoordinates

theorem tendsto_of_uniformly_close_sequences {a : ℕ → ℕ → ℝ} {b e : ℕ → ℝ}
    {u : ℕ → ℝ} {v : ℝ}
    (ha : ∀ j, Tendsto (a j) atTop (𝓝 (b j)))
    (he : Tendsto e atTop (𝓝 0))
    (hu : ∀ j k, dist (u k) (a j k) ≤ e j)
    (hv : ∀ j, dist (b j) v ≤ e j) : Tendsto u atTop (𝓝 v) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := Metric.tendsto_atTop.mp he (ε / 3) (by positivity)
  have hej : e j < ε / 3 := (le_abs_self _).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hj j le_rfl)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (ha j) (ε / 3) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have htri := dist_triangle4 (u k) (a j k) (b j) v
  have hmid := hN k hk
  have hleft := hu j k
  have hright := hv j
  linarith

end RegularPointCoordinates

end OAI
