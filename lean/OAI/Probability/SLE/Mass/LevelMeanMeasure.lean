import OAI.Probability.SLE.Mass.HalfPlaneLevelMeasures
import OAI.Probability.SLE.Mass.LevelApproximationMean
import OAI.Probability.SLE.Mass.RadonKernelIntegral

namespace OAI

/-! The exact mean measure of every terminal level approximation. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

def initialGreenMeasure (κ : ℝ) : Measure upperHalfPlane :=
  (volume.withDensity (fun z => ENNReal.ofReal (initialGreen κ z))).comap Subtype.val

lemma initialGreenMeasure_finite_on_compacts (κ : ℝ) :
    IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := by
  constructor
  intro K hK
  let L := (Subtype.val : upperHalfPlane → ℂ) '' K
  have hL : IsCompact L := hK.image continuous_subtype_val
  have hLH : L ⊆ upperHalfPlane := by rintro _ ⟨x,_,rfl⟩; exact x.property
  obtain ⟨C,hC⟩ := hL.bddAbove_image ((initialGreen_continuousOn κ).mono hLH)
  rw [initialGreenMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    withDensity_apply _ hL.measurableSet]
  apply lt_of_le_of_lt (setLIntegral_mono' hL.measurableSet (fun z hz =>
    ENNReal.ofReal_le_ofReal (hC ⟨z,hz,rfl⟩)))
  rw [setLIntegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL.measure_lt_top

lemma halfPlaneLevelMeasure_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0∞) : Measurable (halfPlaneLevelMeasure κ B γ G u t) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [halfPlaneLevelMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet]
  exact levelApproximation_measurable_apply hm hBc κ u hu γ G F hw t hAI

theorem halfPlaneLevelMeasure_terminal_mean
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : 0 ≤ u) :
    P.bind (halfPlaneLevelMeasure κ B γ G u ∞) = initialGreenMeasure κ := by
  apply Measure.ext
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  have hAH : (Subtype.val : upperHalfPlane → ℂ) '' A ⊆ upperHalfPlane := by
    rintro _ ⟨x,_,rfl⟩; exact x.property
  rw [Measure.bind_apply hA (halfPlaneLevelMeasure_measurable hm hBc κ u hu γ G F hw ∞).aemeasurable]
  simp only [halfPlaneLevelMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    levelApproximation_apply_top κ B γ G u _ hAI]
  rw [initialGreenMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    withDensity_apply _ hAI]
  exact levelMass_mean hB hm hBm hBc hB0 hκ hκ8 γ G F hw _ hAI hAH u hu

theorem halfPlaneLevelMeasure_terminal_test_mean
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : 0 ≤ u) (f : C_c(upperHalfPlane,ℝ)) :
    (∫ ω, (∫ z, f z ∂halfPlaneLevelMeasure κ B γ G u ∞ ω) ∂P) =
      ∫ z, f z ∂initialGreenMeasure κ := by
  have he := halfPlaneLevelMeasure_terminal_mean hB hm hBm hBc hB0 hκ hκ8 γ G F hw u hu
  rw [← he]
  apply integral_bind_of_integrable_sections P _
    (halfPlaneLevelMeasure_measurable hm hBc κ u hu γ G F hw ∞) f f.continuous.measurable
  · intro ω
    let := halfPlaneLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω) u ∞
    exact f.integrable
  · rw [he]
    let := initialGreenMeasure_finite_on_compacts κ
    exact f.integrable

end SLEExactGauge.Multipoint

end

end OAI
