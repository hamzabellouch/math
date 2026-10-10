import OAI.Analysis.FiniteFactor.CrossedProduct.AssignedBadEvents
import OAI.Analysis.FiniteFactor.Convolution

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The source omitted-index masks. Near tagged indices and retained terms
have empty masks. Far assignments depend on n,v and fixed angles only. -/
def sourceOmittedBadEvent (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n v : ℤ) (b : Bool) :
    Set SourceBiasedSample :=
  if h : (((sourceStageState j).K : ℤ) < |v| ∨ ((sourceStageState j).K : ℤ) < |n+v|) ∧
      sourcePhaseLower j < |(omittedIndex (sourceStageState j).K n v : ℝ)| then
    (sourceChosenAssignment θ hθ j hphase (omittedIndex (sourceStageState j).K n v) h.2.le).badEvent b
  else ∅

theorem sourceOmittedBadEvent_measurable (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n v : ℤ) (b : Bool) :
    MeasurableSet (sourceOmittedBadEvent θ hθ j hphase n v b) := by
  unfold sourceOmittedBadEvent
  split_ifs
  · exact SourcePhaseAssignment.badEvent_measurable _ _
  · exact MeasurableSet.empty

/-- All actual omitted masks obey the same conditional bound, in each
orientation and simultaneously over every integer shift and coefficient. -/
theorem sourceOmittedBadEvent_condExp (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ∀ (n v : ℤ) (b : Bool),
      (sourceBiasedLaw j)[(sourceOmittedBadEvent θ hθ j hphase n v b).indicator (fun _ => (1 : ℝ)) |
        (inferInstance : MeasurableSpace (SourceCoordinate → ℝ)).comap
          (sourceBiasedEndpoint (fun _ => b))] ω ≤ Real.exp (-(sourceStage j).L/400) := by
  simp only [ae_all_iff]
  intro n v b
  unfold sourceOmittedBadEvent
  split_ifs
  · exact SourcePhaseAssignment.badEvent_condExp _ b
  · filter_upwards [] with ω
    simp only [Set.indicator_empty]
    change (sourceBiasedLaw j)[(0 : SourceBiasedSample → ℝ) | _] ω ≤ _
    rw [condExp_zero]
    exact (Real.exp_pos _).le

end
end FiniteFactor

end OAI
