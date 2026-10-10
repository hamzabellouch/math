import OAI.Geometry.RCD.Metric.MeasurablePointedApproximation

namespace OAI

/-! # Measurable pointed maps along the same scale sequence -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [MetricSpace Y] [MeasurableSpace Y]

theorem measurable_pointed_sequence {q : Y} {S : ℝ} (hS : 0 < S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hr : ∀ k, 0 < r k) (hε : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) S (ε k) (V k)) :
    ∃ δ : ℕ → ℝ, ∃ W : ℕ → X → Y, Tendsto δ atTop (𝓝 0) ∧
      (∀ k, Measurable (W k)) ∧
      ∀ k, IsPointedApproximation (p k) q (r k) S (δ k) (W k) := by
  let e := fun k : ℕ => ε k+1/((k:ℝ)+1)
  have hep k : 0 < e k := by
    have he0 : 0 ≤ ε k := dist_nonneg.trans (hV k).1
    dsimp only [e]
    positivity
  have heV k := (hV k).mono_error (show ε k ≤ e k by
    dsimp only [e]
    exact le_add_of_nonneg_right (by positivity))
  have hex k := (heV k).exists_measurable (hr k) hS (hep k)
  choose W hWm hW using hex
  refine ⟨fun k => 5*e k,W,?_,hWm,hW⟩
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [add_zero] using hε.add tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [mul_zero] using he.const_mul 5

end RegularPointCoordinates

end

end OAI
