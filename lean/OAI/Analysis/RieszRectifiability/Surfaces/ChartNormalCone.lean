import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem normal_projection_bound_on_chart_range {X : Type*} [PseudoMetricSpace X] {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (H : X → Ambient d) (K L : ℝ≥0)
    (hNormal : LipschitzWith K (fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (H u)))
    (hSep : AntilipschitzWith L H)
    (x : Ambient d) (hx : x ∈ Set.range H) (y : Ambient d) (hy : y ∈ Set.range H) :
    ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
      ((K * L : ℝ≥0) : ℝ) * dist x y := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have h := hNormal.dist_le_mul u v
  rw [dist_eq_norm, ← map_sub] at h
  calc
    _ ≤ (K : ℝ) * dist u v := h
    _ ≤ (K : ℝ) * ((L : ℝ) * dist (H u) (H v)) :=
      mul_le_mul_of_nonneg_left (hSep.le_mul_dist u v) K.coe_nonneg
    _ = _ := by rw [NNReal.coe_mul]; ring

end

end RieszRectifiability

end OAI
