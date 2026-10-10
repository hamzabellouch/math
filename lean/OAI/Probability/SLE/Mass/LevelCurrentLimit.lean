import OAI.Probability.SLE.Mass.LevelRemainderMeasure
import OAI.Probability.SLE.Mass.LevelGreenLimit

namespace OAI

/-! Increasing finite-level remaining kernels converge to the actual killed
Green kernel, also after averaging on an arbitrary event. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

def halfPlaneGreenMeasure {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (t : ℝ≥0) (ω : Ω) : Measure upperHalfPlane :=
  (volume.withDensity (fun z => ENNReal.ofReal
    (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z))).comap Subtype.val

lemma halfPlaneGreenMeasure_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) : Measurable (halfPlaneGreenMeasure κ B γ G t) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [halfPlaneGreenMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    withDensity_apply _ hAI]
  exact (actual_greenDensity_joint_measurable hBm hBc κ γ G F hw t).ennreal_ofReal.lintegral_prod_right'

lemma levelCurrentGreen_le_green
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hw : IsCapacityTwoWitness
      (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (t : ℝ≥0) (z : ℂ) :
    levelCurrentGreen κ B γ G u t z ω ≤
      greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z := by
  unfold levelCurrentGreen
  split_ifs
  · exact le_rfl
  · exact greenDensity_nonneg hw κ t z

lemma halfPlaneCurrentMeasure_le_green
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hw : IsCapacityTwoWitness
      (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω)) (u : ℝ) (t : ℝ≥0) :
    halfPlaneCurrentMeasure κ B γ G u t ω ≤ halfPlaneGreenMeasure κ B γ G t ω := by
  apply Measure.le_iff.mpr
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [halfPlaneCurrentMeasure,halfPlaneGreenMeasure,
    comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,withDensity_apply _ hAI]
  exact lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (levelCurrentGreen_le_green ω hw u t z))

theorem currentGreen_spatial_mean_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {B : ℝ≥0 → Ω → ℝ} (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ : ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (t : ℝ≥0) (K : Set ℂ)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) (E : Set Ω) :
    Tendsto (fun n => ∫⁻ ω in E, (∫⁻ z in K,
      f z * ENNReal.ofReal (levelCurrentGreen κ B γ G (u n) t z ω) ∂volume) ∂P)
      atTop (𝓝 (∫⁻ ω in E, (∫⁻ z in K, f z * ENNReal.ofReal
        (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z) ∂volume) ∂P)) := by
  let a (n : ℕ) (q : Ω × ℂ) :=
    f q.2 * ENNReal.ofReal (levelCurrentGreen κ B γ G (u n) t q.2 q.1)
  have ha (n : ℕ) : Measurable (a n) :=
    (hf.comp measurable_snd).mul
      (levelCurrentGreen_joint_measurable hBm hBc κ (u n) (hu n) γ G F hw t).ennreal_ofReal
  have ham (ω : Ω) : Monotone (fun n => fun z => a n (ω,z)) := by
    intro n m hnm z
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
      (levelCurrentGreen_mono ω (hBc ω) (hw ω) z t (hu n) (hmono hnm)))
  have hal (ω : Ω) : Tendsto (fun n => ∫⁻ z in K, a n (ω,z)) atTop
      (𝓝 (∫⁻ z in K, f z * ENNReal.ofReal
        (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z))) := by
    apply lintegral_tendsto_of_tendsto_of_monotone (μ := volume.restrict K)
      (f := fun n z => a n (ω,z))
      (fun n => ((ha n).comp (measurable_const.prodMk measurable_id)).aemeasurable)
      (Eventually.of_forall (fun z n m hnm => ham ω hnm z))
    filter_upwards [] with z
    apply tendsto_const_nhds.congr'
    exact (levelCurrentGreen_eventually_eq ω (hBc ω) (hw ω) z t u hu hlim).mono
      (fun n hn => congrArg (fun x : ℝ => f z * ENNReal.ofReal x) hn.symm)
  exact lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (ha n).lintegral_prod_right'.aemeasurable)
    (Eventually.of_forall (fun ω n m hnm => lintegral_mono (ham ω hnm)))
    (Eventually.of_forall hal)

theorem halfPlaneCurrentMeasure_mean_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {B : ℝ≥0 → Ω → ℝ} (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ : ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (t : ℝ≥0) (E : Set Ω)
    (A : Set upperHalfPlane) (hA : MeasurableSet A) :
    Tendsto (fun n => (P.restrict E).bind (halfPlaneCurrentMeasure κ B γ G (u n) t) A)
      atTop (𝓝 ((P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t) A)) := by
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [Measure.bind_apply hA
    (halfPlaneCurrentMeasure_measurable hBm hBc κ (u _) (hu _) γ G F hw t).aemeasurable,
    Measure.bind_apply hA (halfPlaneGreenMeasure_measurable hBm hBc κ γ G F hw t).aemeasurable,
    halfPlaneCurrentMeasure,halfPlaneGreenMeasure,
    comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,withDensity_apply _ hAI]
  simpa only [one_mul] using currentGreen_spatial_mean_tendsto P hBm hBc κ γ G F hw
    u hu hmono hlim t _ (fun _ => 1) measurable_const E

theorem halfPlaneGreenMeasure_mean_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) (E : Set Ω) :
    (P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t) ≤ initialGreenMeasure κ := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  apply Measure.le_iff.mpr
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  have hAH : (Subtype.val : upperHalfPlane → ℂ) '' A ⊆ upperHalfPlane := by
    rintro _ ⟨x,_,rfl⟩; exact x.property
  rw [Measure.bind_apply hA (halfPlaneGreenMeasure_measurable hBm hBc κ γ G F hw t).aemeasurable]
  simp only [halfPlaneGreenMeasure,initialGreenMeasure,
    comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,withDensity_apply _ hAI]
  apply (lintegral_mono' Measure.restrict_le_self (le_refl _)).trans
  rw [lintegral_lintegral_swap
    (actual_greenDensity_joint_measurable hBm hBc κ γ G F hw t).ennreal_ofReal.aemeasurable]
  exact setLIntegral_mono' hAI (fun z hz =>
    greenDensity_mean_le hB hBm hBc hB0 hκ hκ8 γ G F hw z (hAH hz) t)

end SLEExactGauge.Multipoint

end

end OAI
