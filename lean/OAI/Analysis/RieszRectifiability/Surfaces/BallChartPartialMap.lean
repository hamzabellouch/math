import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
# Ball charts as ambient parameter maps

A chart on a parameter ball is extended by zero outside its domain. On the ball,
this ambient map agrees with the chart and retains its Lipschitz bound.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

def ballChartPartialMap {n d : ℕ} (r : ℝ)
    (g : ball (0 : Ambient n) r → Ambient d) (u : Ambient n) : Ambient d := by
  classical
  exact if hu : u ∈ ball (0 : Ambient n) r then g ⟨u, hu⟩ else 0

theorem ballChartPartialMap_apply {n d : ℕ} (r : ℝ)
    (g : ball (0 : Ambient n) r → Ambient d) (u : Ambient n) (hu : u ∈ ball (0 : Ambient n) r) :
    ballChartPartialMap r g u = g ⟨u, hu⟩ := by
  simp only [ballChartPartialMap, dite_eq_left hu]

theorem ballChartPartialMap_lipschitzOn {n d : ℕ} (r : ℝ)
    (g : ball (0 : Ambient n) r → Ambient d) (M : ℝ≥0) (hg : LipschitzWith M g) :
    LipschitzOnWith M (ballChartPartialMap r g) (ball (0 : Ambient n) r) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [ballChartPartialMap_apply r g x hx, ballChartPartialMap_apply r g y hy]
  exact hg.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩

theorem ballChartPartialMap_image {n d : ℕ} (r : ℝ)
    (g : ball (0 : Ambient n) r → Ambient d) :
    ballChartPartialMap r g '' ball (0 : Ambient n) r = Set.range g := by
  apply Set.Subset.antisymm
  · rintro y ⟨u, hu, rfl⟩
    rw [ballChartPartialMap_apply r g u hu]
    exact Set.mem_range_self (⟨u, hu⟩ : ball (0 : Ambient n) r)
  · rintro y ⟨u, rfl⟩
    exact ⟨u.val, u.property, ballChartPartialMap_apply r g u.val u.property⟩

end

end RieszRectifiability

end OAI
