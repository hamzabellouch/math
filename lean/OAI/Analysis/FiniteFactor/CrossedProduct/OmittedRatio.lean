import OAI.Analysis.FiniteFactor.CrossedProduct.OmittedBadEvents
import OAI.Analysis.FiniteFactor.CrossedProduct.TagGeometry
import OAI.Analysis.FiniteFactor.CrossedProduct.ConvolutionCocycle

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The source two-ratio inequality and deterministic omitted-index choice
turn tagged and phase attenuation into the pointwise error majorant. -/
theorem sourceOmitted_ratio_bound (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n v : ℤ) (hn : 0 ≤ n)
    (hv : ((sourceStageState j).K : ℤ) < |v| ∨ ((sourceStageState j).K : ℤ) < |n+v|) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ω ∈ sourceTagEndpointEvent j →
      sourceCocycle θ sourceLogWeight (n+v) (sourceBiasedEndpoint (fun _ => true) ω) /
        sourceCocycle θ sourceLogWeight v (sourceBiasedEndpoint (fun _ => false) ω) ≤
          Real.exp (-(sourceStage j).L) +
            (sourceOmittedBadEvent θ hθ j hphase n v false).indicator (fun _ => (1 : ℝ)) ω +
            (sourceOmittedBadEvent θ hθ j hphase n v true).indicator (fun _ => (1 : ℝ)) ω := by
  let k := omittedIndex (sourceStageState j).K n v
  have hk := omittedIndex_spec (sourceStageState j).K n v hv
  have hlarge : ∀ᵐ ω ∂sourceBiasedLaw j,
      sourcePhaseLower j < |(k : ℝ)| →
      sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => true) ω) /
        sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => false) ω) ≤
          Real.exp (-(sourceStage j).L) ∨
        ω ∈ sourceOmittedBadEvent θ hθ j hphase n v false ∨
        ω ∈ sourceOmittedBadEvent θ hθ j hphase n v true := by
    by_cases hh : sourcePhaseLower j < |(k : ℝ)|
    · have ha := (sourceChosenAssignment θ hθ j hphase k hh.le).attenuation_or_bad hθ
      filter_upwards [ha] with ω hω _
      have htest : (((sourceStageState j).K : ℤ) < |v| ∨ ((sourceStageState j).K : ℤ) < |n+v|) ∧
          sourcePhaseLower j < |(omittedIndex (sourceStageState j).K n v : ℝ)| := ⟨hv,hh⟩
      simpa only [sourceOmittedBadEvent,dite_eq_left htest] using hω
    · exact Eventually.of_forall fun ω h => (hh h).elim
  filter_upwards [hlarge,sourceTagEndpoint_attenuation θ hθ j,
    sourceBiasedEndpoint_ae j (fun _ => false) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedEndpoint_ae j (fun _ => true) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedLaw_ordered j] with ω hfar htag hfx hfy hxy
  intro he
  let x := sourceBiasedEndpoint (fun _ => false) ω
  let y := sourceBiasedEndpoint (fun _ => true) ω
  have hb := cocycle_two_ratio_bounds
    (fun k => sourceCocycle_pos θ sourceLogWeight k x)
    (fun k => sourceCocycle_pos θ sourceLogWeight k y)
    (sourceCocycle_antitone θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hfx)
    (sourceCocycle_antitone θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hfy)
    (sourceCocycle_ordered θ sourceLogWeight sourceLogWeight_nonneg hfx hfy hxy)
    (v := v) hn
  have hratio : sourceCocycle θ sourceLogWeight (n+v) y / sourceCocycle θ sourceLogWeight v x ≤
      sourceCocycle θ sourceLogWeight k y / sourceCocycle θ sourceLogWeight k x := by
    rcases hk.2 with h | h
    · rw [show k = v from h]
      exact hb.2.1.trans (min_le_left _ _)
    · rw [show k = n+v from h]
      exact hb.2.1.trans (min_le_right _ _)
  have h1 := hb.2.1.trans hb.2.2
  have hbad0 (b : Bool) : 0 ≤ (sourceOmittedBadEvent θ hθ j hphase n v b).indicator (fun _ => (1 : ℝ)) ω := by
    by_cases h : ω ∈ sourceOmittedBadEvent θ hθ j hphase n v b <;> simp [h]
  have hpos := (Real.exp_pos (-(sourceStage j).L)).le
  by_cases hh : sourcePhaseLower j < |(k : ℝ)|
  · rcases hfar hh with h | h | h
    · have hle := hratio.trans h
      linarith [hbad0 false,hbad0 true]
    · rw [Set.indicator_of_mem h]
      linarith [hbad0 true]
    · rw [Set.indicator_of_mem h]
      linarith [hbad0 false]
  · have hklo : ((sourceStageState j).K : ℝ) ≤ |(k : ℝ)| := by
      have hki : ((sourceStageState j).K : ℤ) < |k| := hk.1
      exact_mod_cast hki.le
    have hh' := htag he k hklo (le_of_not_gt hh)
    have hle := hratio.trans hh'
    linarith [hbad0 false,hbad0 true]

end
end FiniteFactor

end OAI
