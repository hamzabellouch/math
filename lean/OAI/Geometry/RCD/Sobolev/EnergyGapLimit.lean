import OAI.Geometry.RCD.Sobolev.QuadraticEnergyLimit

namespace OAI

/-! # Vanishing nonnegative energy gaps from sharp one-sided bounds -/

open Filter
open scoped Topology
namespace RegularPointCoordinates

theorem energy_gap_tendsto_zero {D E F e : ℕ → ℝ} {A : ℝ}
    (hD : ∀ k, 0≤D k) (hid : ∀ k, D k=E k-F k+e k)
    (hE : Tendsto E atTop (𝓝 A))
    (hF : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, A-δ≤F k)
    (he : Tendsto e atTop (𝓝 0)) : Tendsto D atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hδ4 : 0<δ/4 := by positivity
  have hEu := hE.eventually (Iio_mem_nhds (show A<A+δ/4 by linarith))
  have heu := he.eventually (Iio_mem_nhds hδ4)
  filter_upwards [hEu,hF (δ/4) hδ4,heu] with k hEk hFk hek
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hD k),hid k]
  linarith

theorem poisson_energy_gap_tendsto_zero {D E F S T : ℕ → ℝ} {A : ℝ}
    (hD : ∀ k, 0≤D k) (hid : ∀ k, D k=E k-F k-2*S k-4*T k)
    (hE : Tendsto E atTop (𝓝 A))
    (hF : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, A-δ≤F k)
    (hS : Tendsto S atTop (𝓝 0)) (hT : Tendsto T atTop (𝓝 0)) :
    Tendsto D atTop (𝓝 0) := by
  apply energy_gap_tendsto_zero (E := E) (F := F) (A := A) hD (e := fun k => -2*S k-4*T k)
  · intro k
    rw [hid k]
    ring
  · exact hE
  · exact hF
  · convert ((hS.const_mul (-2)).sub (hT.const_mul 4)) using 1
    norm_num

end RegularPointCoordinates

end OAI
