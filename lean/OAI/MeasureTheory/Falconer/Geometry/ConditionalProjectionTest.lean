import OAI.MeasureTheory.Falconer.Geometry.ProjectionExceptional
import OAI.MeasureTheory.Falconer.Geometry.ConditionalProjectionBuffer

namespace OAI

/-! # Literal occupied-anchor projection tests -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem projectionGoodSet_mono_width (μ : Measure (Space d)) {W W' T : ℝ} (hW : W ≤ W') :
    projectionGoodSet μ W' T ⊆ projectionGoodSet μ W T := by
  intro w hw
  apply le_trans (measure_mono ?_) hw
  intro z hz
  exact hz.trans hW

namespace Regularization

noncomputable def conditionalProjectionGoodSet (Q : DyadicCube d) (ρ : Measure (Space d))
    (P : CellPath d) (W T : ℝ) : Set (Sphere d) :=
  if 0 < ρ (Q.descendant P).carrier then
    projectionGoodSet (ProbabilityTheory.cond ρ (Q.descendant P).carrier) W T else ∅

theorem conditionalProjectionGoodSet_measurable (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d) (W T : ℝ) :
    MeasurableSet (conditionalProjectionGoodSet Q ρ P W T) := by
  classical
  unfold conditionalProjectionGoodSet
  split_ifs
  · exact measurableSet_projectionGoodSet _ _ _
  · exact MeasurableSet.empty

theorem conditionalProjectionGoodSet_buffer (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d)
    {δ W W' T : ℝ} (hδ : 0 ≤ δ) {v w : Sphere d} (hvw : dist v w ≤ δ)
    (hwidth : W+(Real.sqrt d/(2:ℝ)^P.length)*δ ≤ W')
    (hw : w ∈ conditionalProjectionGoodSet Q ρ P W' T) :
    v ∈ conditionalProjectionGoodSet Q ρ P W T := by
  classical
  unfold conditionalProjectionGoodSet at hw ⊢
  split_ifs at hw ⊢ with hocc
  · exact conditional_projection_buffer Q hQ ρ P hδ hvw hwidth hw
  · exact False.elim hw

theorem conditionalProjectionGoodSet_mono_width (Q : DyadicCube d) (ρ : Measure (Space d))
    (P : CellPath d) {W W' T : ℝ} (hW : W ≤ W') :
    conditionalProjectionGoodSet Q ρ P W' T ⊆ conditionalProjectionGoodSet Q ρ P W T := by
  classical
  unfold conditionalProjectionGoodSet
  split_ifs
  · exact projectionGoodSet_mono_width _ hW
  · exact Subset.rfl

end Regularization
end Falconer

end OAI
