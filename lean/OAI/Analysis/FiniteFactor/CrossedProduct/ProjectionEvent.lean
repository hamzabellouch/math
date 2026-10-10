import OAI.Analysis.FiniteFactor.CrossedProduct.FiniteCoefficients
import OAI.Analysis.FiniteFactor.CrossedProduct.TagLaw
import OAI.Analysis.FiniteFactor.CrossedProduct.StagePolynomial

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section

def sourceDiagonalEvent
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (j : ℕ) : Set SourceBiasedSample :=
  {ω | 1/((j : ℝ)+1) ≤ (sourceCentralCoefficient p (sourceBiasedEndpoint (fun _ => false) ω)).re ∧
    1/((j : ℝ)+1) ≤ 1-(sourceCentralCoefficient p (sourceBiasedEndpoint (fun _ => true) ω)).re}

theorem sourceDiagonalEvent_measurable
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (j : ℕ) :
    MeasurableSet (sourceDiagonalEvent p j) := by
  have hm (b : Bool) : Measurable (fun ω => (sourceCentralCoefficient p
      (sourceBiasedEndpoint (fun _ => b) ω)).re) :=
    Complex.continuous_re.measurable.comp ((sourceCentralCoefficient_measurable p).comp
      (sourceBiasedEndpoint_measurable _))
  exact (measurableSet_le measurable_const (hm false)).inter
    (measurableSet_le measurable_const (measurable_const.sub (hm true)))

/-- The actual three conditions defining E_j in the source, with j+1 indexing. -/
def sourceProjectionEvent
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (j : ℕ) : Set SourceBiasedSample :=
  sourceTaggedEvent j ∩ sourceBoundaryEvent j ∩ sourceDiagonalEvent p j

theorem sourceProjectionEvent_measurable
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (j : ℕ) :
    MeasurableSet (sourceProjectionEvent p j) :=
  ((sourceTaggedEvent_measurable j).inter (sourceBoundaryEvent_measurable j)).inter
    (sourceDiagonalEvent_measurable p j)

/-- The zero coefficient bounds use the actual diagonal and F_0=1. -/
theorem sourceProjection_zero_coefficients (θ : SourceCoordinate → ℝ)
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (j : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ω ∈ sourceDiagonalEvent p j →
      1/((j : ℝ)+1) ≤ ‖sourceProjectionLeftCoefficient θ p (sourceBiasedEndpoint (fun _ => false) ω) 0‖ ∧
      1/((j : ℝ)+1) ≤ ‖sourceProjectionRightCoefficient θ p (sourceBiasedEndpoint (fun _ => true) ω) 0‖ := by
  filter_upwards [sourceBiasedEndpoint_cube j (fun _ => false),sourceBiasedEndpoint_cube j (fun _ => true)]
    with ω hxc hyc
  intro he
  constructor
  · have hz : sourceProjectionLeftCoefficient θ p (sourceBiasedEndpoint (fun _ => false) ω) 0 =
        sourceCentralCoefficient p (sourceBiasedEndpoint (fun _ => false) ω) := by
      simp only [sourceProjectionLeftCoefficient,leftCoefficient,sourceCocycle_zero θ sourceLogWeight hxc,
        Complex.ofReal_one,div_one]
      rfl
    rw [hz]
    exact he.1.trans (Complex.re_le_norm _)
  · have hz : sourceProjectionRightCoefficient θ p (sourceBiasedEndpoint (fun _ => true) ω) 0 =
        conj (1-sourceCentralCoefficient p (sourceBiasedEndpoint (fun _ => true) ω)) := by
      simp only [sourceProjectionRightCoefficient,rightCoefficient,neg_zero,
        sourceCocycle_zero θ sourceLogWeight hyc,Complex.ofReal_one,one_mul]
      congr 1
    rw [hz,RCLike.norm_conj]
    have hh := Complex.re_le_norm (1-sourceCentralCoefficient p (sourceBiasedEndpoint (fun _ => true) ω))
    exact he.2.trans (by simpa only [Complex.sub_re,Complex.one_re] using hh)

/-- The actual source-stage polynomial lower bound holds on the exact E_j.
This theorem does not assert that E_j has positive probability. -/
theorem sourceProjectionEvent_polynomial_lower (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) (j : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ω ∈ sourceProjectionEvent p j →
      (sourceStage j).ε ≤ coefficientMass (sourceStageState j).K
        (sourceProjectionLeftCoefficient θ p (sourceBiasedEndpoint (fun _ => false) ω))
        (sourceProjectionRightCoefficient θ p (sourceBiasedEndpoint (fun _ => true) ω)) := by
  filter_upwards [sourceProjection_finite_coefficients θ hθ hp hproj j,
    sourceProjection_zero_coefficients θ p j] with ω hc hz
  intro he
  apply sourceStage_polynomial_lower
  · intro k hklo hkhi
    exact (hc he.1.2 k (by exact_mod_cast abs_le.mpr ⟨hklo,hkhi⟩)).1
  · intro k hklo hkhi
    exact (hc he.1.2 k (by exact_mod_cast abs_le.mpr ⟨hklo,hkhi⟩)).2
  · exact (hz he.2).1
  · exact (hz he.2).2

end
end FiniteFactor

end OAI
