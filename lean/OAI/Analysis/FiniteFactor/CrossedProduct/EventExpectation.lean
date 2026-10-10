import OAI.Analysis.FiniteFactor.CrossedProduct.TruncatedBound

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The source per-coefficient expectation upper bound, with all convolution,
ratio and masked-error inputs discharged for the original invariant p. -/
theorem sourceProjectionEvent_coefficient_expectation (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n : ℕ) :
    (∫ ω in sourceProjectionEvent p j, ‖sourceTruncatedCoefficient θ p j n ω‖ ∂sourceBiasedLaw j) ≤
      Real.exp (-(sourceStage j).L)+2*Real.exp (-(sourceStage j).L/800) := by
  let E := sourceProjectionEvent p j
  let e := sourceOmittedError θ hθ p j hphase (n : ℤ)
  let a := Real.exp (-(sourceStage j).L)
  have hE := sourceProjectionEvent_measurable p j
  have hi := (sourceTruncatedCoefficient_integrable θ hθ hs hp hproj hinv j n).norm
  obtain ⟨hi0,hb0⟩ := sourceOmittedError_estimate θ hθ hp hproj j hphase n false
  obtain ⟨hi1,hb1⟩ := sourceOmittedError_estimate θ hθ hp hproj j hphase n true
  have hmajor : ∀ᵐ ω ∂sourceBiasedLaw j,
      E.indicator (fun ω => ‖sourceTruncatedCoefficient θ p j n ω‖) ω ≤ a+e false ω+e true ω := by
    filter_upwards [sourceProjectionEvent_error_pointwise θ hθ hs hp hproj hinv j hphase n] with ω hω
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he]
      exact hω he
    · rw [Set.indicator_of_notMem he]
      exact add_nonneg (add_nonneg (Real.exp_pos _).le (sourceOmittedError_nonneg ..)) (sourceOmittedError_nonneg ..)
  have hh := integral_mono_ae (hi.indicator hE) (((integrable_const a).add hi0).add hi1) hmajor
  rw [integral_indicator hE] at hh
  have he1 := integral_add ((integrable_const a).add hi0) hi1
  have he0 := integral_add (integrable_const a) hi0
  dsimp only [Pi.add_apply] at he1 he0 hh
  rw [he1,he0] at hh
  have ha : (∫ _ω : SourceBiasedSample, a ∂sourceBiasedLaw j) = a := by simp
  rw [ha] at hh
  change _ ≤ a+2*Real.exp (-(sourceStage j).L/800)
  linarith

end
end FiniteFactor

end OAI
