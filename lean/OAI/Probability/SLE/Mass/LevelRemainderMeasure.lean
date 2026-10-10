import OAI.Probability.SLE.Mass.LevelApproximationKernel
import OAI.Probability.SLE.Mass.LevelMeanMeasure

namespace OAI

/-! The unreached part of a finite-level approximation, as a positive
measure. The conditional Green identity holds as a measure identity. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

def halfPlaneRemainderMeasure {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (t : ℝ≥0) (ω : Ω) : Measure upperHalfPlane :=
  (volume.withDensity (fun z => ENNReal.ofReal (levelRemainderGreen κ B γ G u t z ω))).comap Subtype.val

def halfPlaneCurrentMeasure {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (t : ℝ≥0) (ω : Ω) : Measure upperHalfPlane :=
  (volume.withDensity (fun z => ENNReal.ofReal (levelCurrentGreen κ B γ G u t z ω))).comap Subtype.val

lemma levelDensity_split {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (t : ℝ≥0) (ω : Ω) (z : ℂ) :
    levelApproximationDensity κ B γ G u ∞ ω z =
      levelApproximationDensity κ B γ G u t ω z +
        ENNReal.ofReal (levelRemainderGreen κ B γ G u t z ω) := by
  unfold levelApproximationDensity levelRemainderGreen
  by_cases h : radiusLevelTime (γ ω) (G ω) z u ≤ t
  · simp only [le_top,ite_true,ite_eq_left h,ite_eq_right (not_lt.mpr h),
      ENNReal.ofReal_zero,add_zero]
  · simp only [le_top,ite_true,ite_eq_right h,ite_eq_left (lt_of_not_ge h),zero_add]

lemma halfPlaneRemainderMeasure_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) : Measurable (halfPlaneRemainderMeasure κ B γ G u t) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [halfPlaneRemainderMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    withDensity_apply _ hAI]
  exact (levelRemainderGreen_joint_measurable hm hBc κ u hu γ G F hw t).ennreal_ofReal.lintegral_prod_right'

lemma halfPlaneCurrentMeasure_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) : Measurable (halfPlaneCurrentMeasure κ B γ G u t) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [halfPlaneCurrentMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    withDensity_apply _ hAI]
  exact (levelCurrentGreen_joint_measurable hBm hBc κ u hu γ G F hw t).ennreal_ofReal.lintegral_prod_right'

lemma halfPlaneLevelMeasure_split
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) (ω : Ω) :
    halfPlaneLevelMeasure κ B γ G u ∞ ω =
      halfPlaneLevelMeasure κ B γ G u t ω + halfPlaneRemainderMeasure κ B γ G u t ω := by
  apply Measure.ext
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [Measure.add_apply,halfPlaneLevelMeasure,halfPlaneRemainderMeasure,levelApproximation,
    comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,withDensity_apply _ hAI]
  simp_rw [levelDensity_split κ B γ G u t ω]
  exact lintegral_add_left
    (levelApproximationDensity_joint_measurable hm hBc κ u hu γ G F hw t).of_uncurry_left _

theorem halfPlaneRemainderMeasure_conditional_mean
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0) (E : Set Ω)
    (hE : MeasurableSet[Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable) t] E) :
    (P.restrict E).bind (halfPlaneRemainderMeasure κ B γ G u t) =
      (P.restrict E).bind (halfPlaneCurrentMeasure κ B γ G u t) := by
  let hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  apply Measure.ext
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  have hAH : (Subtype.val : upperHalfPlane → ℂ) '' A ⊆ upperHalfPlane := by
    rintro _ ⟨x,_,rfl⟩; exact x.property
  rw [Measure.bind_apply hA (halfPlaneRemainderMeasure_measurable hm hBc κ u hu γ G F hw t).aemeasurable,
    Measure.bind_apply hA (halfPlaneCurrentMeasure_measurable hBm hBc κ u hu γ G F hw t).aemeasurable]
  simp only [halfPlaneRemainderMeasure,halfPlaneCurrentMeasure,
    comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,withDensity_apply _ hAI]
  simpa only [one_mul] using levelRemainderGreen_spatial_kernel hB hBm hBc hB0 hκ hκ8 γ G F hw
    u hu t _ hAI hAH (fun _ => 1) measurable_const E hE

end SLEExactGauge.Multipoint

end

end OAI
