import OAI.Probability.SLE.Mass.RationalCanonicalMass
import OAI.Probability.SLE.SimpleTails

namespace OAI

/-! The canonical mass has finite expected mass on bounded physical sets,
including sets that approach the real boundary. Compactness inside the
half-plane is not needed for the upper-cover charge. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal

namespace SLEExactGauge.Multipoint

lemma initialGreenMeasure_bounded_ball_lt_top {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8)
    (R : ℝ) :
    initialGreenMeasure κ (Subtype.val ⁻¹' closedBall (0:ℂ) R) < ∞ := by
  let A : Set upperHalfPlane := Subtype.val ⁻¹' closedBall (0:ℂ) R
  have hA : MeasurableSet A := isClosed_closedBall.measurableSet.preimage
    continuous_subtype_val.measurable
  have hI : MeasurableSet ((Subtype.val : upperHalfPlane → ℂ) '' A) :=
    (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  have hsub : (Subtype.val : upperHalfPlane → ℂ) '' A ⊆ closedBall 0 R := by
    rintro _ ⟨z,hz,rfl⟩
    exact hz
  have hi : IntegrableOn (fun z : ℂ => (2:ℝ)^(-codimension κ)*|z.im|^(-codimension κ))
      (closedBall 0 R) volume :=
    (integrable_height_power_ball (codimension κ) R (codimension_lt_one κ hκ)).const_mul _
  change initialGreenMeasure κ A < ∞
  rw [initialGreenMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    withDensity_apply _ hI]
  refine lt_of_le_of_lt ?_ (lintegral_ofReal_lt_top_of_integrable hi)
  calc
    (∫⁻ z in (Subtype.val : upperHalfPlane → ℂ) '' A, ENNReal.ofReal (initialGreen κ z)) ≤
        ∫⁻ z in (Subtype.val : upperHalfPlane → ℂ) '' A,
          ENNReal.ofReal ((2:ℝ)^(-codimension κ)*|z.im|^(-codimension κ)) := by
      apply setLIntegral_mono' hI
      rintro z ⟨w,_,rfl⟩
      apply ENNReal.ofReal_le_ofReal
      simpa only [abs_of_pos (show 0<(w:ℂ).im from w.property)] using
        initialGreen_le_height κ hκ hκ8 w w.property
    _ ≤ _ := lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

lemma RationalCanonicalMass.terminal_bounded_mean_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : RationalCanonicalMass P κ B hBm γ G) (hκ : 0<κ) (hκ8 : κ<8)
    (R : ℝ) :
    (∫⁻ ω, C.terminal ω (Subtype.val ⁻¹' closedBall (0:ℂ) R) ∂P) < ∞ := by
  rw [← Measure.bind_apply
    (isClosed_closedBall.measurableSet.preimage continuous_subtype_val.measurable)
    C.terminal_measurable.aemeasurable,C.mean]
  exact initialGreenMeasure_bounded_ball_lt_top hκ hκ8 R

end SLEExactGauge.Multipoint

end

end OAI
