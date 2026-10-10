import OAI.Analysis.FiniteFactor.CrossedProduct.EventExpectation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- An invariant projection in the original algebra forces the actual source
event to have mass at most 1/(j+1) whenever the fixed-angle phase condition
holds. Every coefficient, convolution and expectation input is discharged. -/
theorem sourceProjectionEvent_mass_upper (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) :
    (sourceBiasedLaw j).real (sourceProjectionEvent p j) ≤ 1/((j : ℝ)+1) := by
  let K := (sourceStageState j).K
  let A := fun ω => sourceProjectionLeftCoefficient θ p (sourceBiasedEndpoint (fun _ => false) ω)
  let B := fun ω => sourceProjectionRightCoefficient θ p (sourceBiasedEndpoint (fun _ => true) ω)
  let Mass := fun ω => coefficientMass K (A ω) (B ω)
  have hi : Integrable Mass (sourceBiasedLaw j) := by
    dsimp only [Mass,coefficientMass]
    exact integrable_finsetSum (Finset.range (2*K+1)) (fun n _ =>
      (sourceTruncatedCoefficient_integrable θ hθ hs hp hproj hinv j n).norm)
  have hlow : (sourceStage j).ε * (sourceBiasedLaw j).real (sourceProjectionEvent p j) ≤
      ∫ ω in sourceProjectionEvent p j, Mass ω ∂sourceBiasedLaw j := by
    have hh := setIntegral_mono_on_ae (integrable_const (sourceStage j).ε) hi.integrableOn
      (sourceProjectionEvent_measurable p j) (sourceProjectionEvent_polynomial_lower θ hθ hp hproj j)
    simpa only [setIntegral_const,smul_eq_mul,mul_comm] using hh
  have hu := coefficientMass_integral_upper K A B (E := sourceProjectionEvent p j)
    (μ := sourceBiasedLaw j)
    (a := Real.exp (-(sourceStage j).L)+2*Real.exp (-(sourceStage j).L/800))
    (fun n _ => (sourceTruncatedCoefficient_integrable θ hθ hs hp hproj hinv j n).norm.integrableOn)
    (fun n _ => sourceProjectionEvent_coefficient_expectation θ hθ hs hp hproj hinv j hphase n)
  have hupper := hu.trans (sourceStage_error_budget j)
  have hh : (sourceStage j).ε * (sourceBiasedLaw j).real (sourceProjectionEvent p j) ≤
      (sourceStage j).ε * (1/((j : ℝ)+1)) := by
    calc
      (sourceStage j).ε * (sourceBiasedLaw j).real (sourceProjectionEvent p j) ≤
          (sourceStage j).ε/((j : ℝ)+1) := hlow.trans hupper
      _ = (sourceStage j).ε * (1/((j : ℝ)+1)) := by ring
  nlinarith [(sourceStage j).ε_pos]

end
end FiniteFactor

end OAI
