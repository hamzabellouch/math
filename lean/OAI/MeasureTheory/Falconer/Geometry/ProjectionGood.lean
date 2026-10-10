import OAI.MeasureTheory.Falconer.Geometry.ProjectionLaw
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-! # Measurable projection tests on the full conditional probability -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem measurable_projectionCollision (μ : Measure (Space d)) [IsFiniteMeasure μ] (W : ℝ) :
    Measurable (fun w : Sphere d => projectionCollision μ (w:Space d) W) := by
  let S := {p : Sphere d × (Space d × Space d) |
    |inner ℝ (p.2.1-p.2.2) (p.1:Space d)| ≤ W}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_le (by fun_prop) measurable_const
  exact measurable_measure_prodMk_left hS

noncomputable def projectionGoodSet (μ : Measure (Space d)) (W T : ℝ) : Set (Sphere d) :=
  {w | projectionCollision μ (w:Space d) W ≤ ENNReal.ofReal T}

theorem measurableSet_projectionGoodSet (μ : Measure (Space d)) [IsFiniteMeasure μ] (W T : ℝ) :
    MeasurableSet (projectionGoodSet μ W T) :=
  measurableSet_le (measurable_projectionCollision μ W) measurable_const

theorem projectionGoodSet_exceptional (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (ν : Measure (Sphere d)) (W : ℝ) {T : ℝ} (hT : 0 < T) :
    ν (projectionGoodSet μ W T)ᶜ ≤
      (∫⁻ w : Sphere d, projectionCollision μ (w:Space d) W ∂ν)/ENNReal.ofReal T := by
  have hsub : (projectionGoodSet μ W T)ᶜ ⊆
      {w : Sphere d | ENNReal.ofReal T ≤ projectionCollision μ (w:Space d) W} := by
    intro w hw
    change ¬ projectionCollision μ (w:Space d) W ≤ ENNReal.ofReal T at hw
    exact (lt_of_not_ge hw).le
  exact (measure_mono hsub).trans (meas_ge_le_lintegral_div
    (measurable_projectionCollision μ W).aemeasurable
    (ENNReal.ofReal_pos.mpr hT).ne' ENNReal.ofReal_ne_top)

end Falconer

end OAI
