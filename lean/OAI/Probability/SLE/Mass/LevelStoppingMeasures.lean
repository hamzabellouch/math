import OAI.Probability.SLE.Mass.LevelStoppingGreenLimit
import OAI.Probability.SLE.Mass.LevelMeanMeasure

namespace OAI

/-! The unreached part of a finite-level approximation at an arbitrary
stopping time, as a positive measure. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

lemma levelApproximationDensity_random_time_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (S : Ω → ℝ≥0∞) (hS : Measurable S) :
    Measurable (fun p : Ω × ℂ => levelApproximationDensity κ B γ G u (S p.1) p.1 p.2) :=
  Measurable.ite (measurableSet_le
    (actual_radiusLevel_joint_measurable hm hc κ u hu γ G F hw) (hS.comp measurable_fst))
    (actual_stoppedGreen_joint_measurable hm hc κ u hu γ G F hw).ennreal_ofReal measurable_const

lemma halfPlaneLevelMeasure_random_time_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (S : Ω → ℝ≥0∞) (hS : Measurable S) :
    Measurable (fun ω => halfPlaneLevelMeasure κ B γ G u (S ω) ω) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [halfPlaneLevelMeasure,levelApproximation,
    comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,withDensity_apply _ hAI]
  exact (levelApproximationDensity_random_time_joint_measurable hm hc κ u hu γ G F hw S hS).lintegral_prod_right'

def halfPlaneStoppingRemainderMeasure {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (S : Ω → ℝ≥0∞) (ω : Ω) : Measure upperHalfPlane :=
  (volume.withDensity (fun z => ENNReal.ofReal (levelStoppingRemainderGreen κ B γ G u S z ω))).comap Subtype.val

def halfPlaneStoppingCurrentMeasure {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (S : Ω → ℝ≥0∞) (ω : Ω) : Measure upperHalfPlane :=
  (volume.withDensity (fun z => ENNReal.ofReal (levelStoppingCurrentGreen κ B γ G u S z ω))).comap Subtype.val

def halfPlaneStoppingGreenMeasure {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (S : Ω → ℝ≥0∞) (ω : Ω) : Measure upperHalfPlane :=
  (volume.withDensity (fun z => ENNReal.ofReal (stoppingGreen κ B γ G S z ω))).comap Subtype.val

lemma stoppingGreen_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : Measurable (Function.uncurry B)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (S : Ω → ℝ≥0∞) (hS : Measurable S) :
    Measurable (fun p : Ω × ℂ => stoppingGreen κ B γ G S p.2 p.1) :=
  Measurable.ite (measurableSet_lt (hS.comp measurable_fst) measurable_const)
    (actual_greenDensity_random_time_joint_measurable hBm hc κ γ G F hw
      (fun ω => (S ω).toNNReal) (ENNReal.measurable_toNNReal.comp hS)) measurable_const

lemma halfPlaneStoppingGreenMeasure_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : Measurable (Function.uncurry B)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (S : Ω → ℝ≥0∞) (hS : Measurable S) :
    Measurable (halfPlaneStoppingGreenMeasure κ B γ G S) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [halfPlaneStoppingGreenMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    withDensity_apply _ hAI]
  exact (stoppingGreen_joint_measurable hBm hc κ γ G F hw S hS).ennreal_ofReal.lintegral_prod_right'

lemma halfPlaneStoppingRemainderMeasure_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (S : Ω → ℝ≥0∞) (hS : Measurable S) : Measurable (halfPlaneStoppingRemainderMeasure κ B γ G u S) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [halfPlaneStoppingRemainderMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    withDensity_apply _ hAI]
  exact (levelStoppingRemainderGreen_joint_measurable hm hBc κ u hu γ G F hw S hS).ennreal_ofReal.lintegral_prod_right'

lemma halfPlaneStoppingCurrentMeasure_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (S : Ω → ℝ≥0∞) (hS : Measurable S) : Measurable (halfPlaneStoppingCurrentMeasure κ B γ G u S) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [halfPlaneStoppingCurrentMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    withDensity_apply _ hAI]
  exact (levelStoppingCurrentGreen_joint_measurable hBm hBc κ u hu γ G F hw S hS).ennreal_ofReal.lintegral_prod_right'

lemma halfPlaneLevelMeasure_stopping_split
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (S : Ω → ℝ≥0∞) (hS : Measurable S) (ω : Ω) :
    halfPlaneLevelMeasure κ B γ G u ∞ ω =
      halfPlaneLevelMeasure κ B γ G u (S ω) ω + halfPlaneStoppingRemainderMeasure κ B γ G u S ω := by
  apply Measure.ext
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [Measure.add_apply,halfPlaneLevelMeasure,halfPlaneStoppingRemainderMeasure,levelApproximation,
    comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,withDensity_apply _ hAI]
  simp_rw [stopping_level_density_split κ B γ G u S ω]
  have hd : Measurable (fun z => levelApproximationDensity κ B γ G u (S ω) ω z) := by
    have hp : Measurable (fun z : ℂ => (ω,z)) := measurable_const.prodMk measurable_id
    have hh := (levelApproximationDensity_random_time_joint_measurable hm hBc κ u hu
      γ G F hw S hS).comp hp
    simpa only [Function.comp_def] using hh
  exact lintegral_add_left hd _

theorem halfPlaneStoppingRemainderMeasure_conditional_mean
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : 0 ≤ u) (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) S)
    (E : Set Ω)
    (hE : MeasurableSet[hS.measurableSpace] E) :
    (P.restrict E).bind (halfPlaneStoppingRemainderMeasure κ B γ G u S) =
      (P.restrict E).bind (halfPlaneStoppingCurrentMeasure κ B γ G u S) := by
  let hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  apply Measure.ext
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  have hAH : (Subtype.val : upperHalfPlane → ℂ) '' A ⊆ upperHalfPlane := by
    rintro _ ⟨x,_,rfl⟩; exact x.property
  rw [Measure.bind_apply hA (halfPlaneStoppingRemainderMeasure_measurable hm hBc κ u hu γ G F hw S hS.measurable').aemeasurable,
    Measure.bind_apply hA (halfPlaneStoppingCurrentMeasure_measurable hBm hBc κ u hu γ G F hw S hS.measurable').aemeasurable]
  simp only [halfPlaneStoppingRemainderMeasure,halfPlaneStoppingCurrentMeasure,
    comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,withDensity_apply _ hAI]
  simpa only [one_mul] using levelStoppingRemainderGreen_spatial_kernel hB hBm hBc hB0 hκ hκ8 γ G F hw
    u hu S hS _ hAI hAH (fun _ => 1) measurable_const E hE

theorem halfPlaneLevelMeasure_stopping_conditional_split
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : 0 ≤ u) (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) S)
    (E : Set Ω) (hE : MeasurableSet[hS.measurableSpace] E) :
    (P.restrict E).bind (halfPlaneLevelMeasure κ B γ G u ∞) =
      (P.restrict E).bind (fun ω => halfPlaneLevelMeasure κ B γ G u (S ω) ω) +
      (P.restrict E).bind (halfPlaneStoppingCurrentMeasure κ B γ G u S) := by
  let hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  rw [← halfPlaneStoppingRemainderMeasure_conditional_mean hB hBm hc hB0 hκ hκ8
    γ G F hw u hu S hS E hE]
  apply Measure.ext
  intro A hA
  rw [Measure.add_apply,
    Measure.bind_apply hA (halfPlaneLevelMeasure_measurable hm hc κ u hu γ G F hw ∞).aemeasurable,
    Measure.bind_apply hA (halfPlaneLevelMeasure_random_time_measurable hm hc κ u hu
      γ G F hw S hS.measurable').aemeasurable,
    Measure.bind_apply hA (halfPlaneStoppingRemainderMeasure_measurable hm hc κ u hu
      γ G F hw S hS.measurable').aemeasurable]
  simp_rw [halfPlaneLevelMeasure_stopping_split hm hc κ u hu γ G F hw S hS.measurable',Measure.add_apply]
  exact lintegral_add_left (((Measure.measurable_coe hA).comp
    (halfPlaneLevelMeasure_random_time_measurable hm hc κ u hu γ G F hw S hS.measurable'))) _

theorem halfPlaneStoppingGreenMeasure_mean_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) S)
    (E : Set Ω) :
    (P.restrict E).bind (halfPlaneStoppingGreenMeasure κ B γ G S) ≤ initialGreenMeasure κ := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  apply Measure.le_iff.mpr
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  have hAH : (Subtype.val : upperHalfPlane → ℂ) '' A ⊆ upperHalfPlane := by
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  rw [Measure.bind_apply hA
    (halfPlaneStoppingGreenMeasure_measurable hBm hc κ γ G F hw S hS.measurable').aemeasurable]
  simp only [halfPlaneStoppingGreenMeasure,initialGreenMeasure,
    comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,withDensity_apply _ hAI]
  apply (lintegral_mono' Measure.restrict_le_self (le_refl _)).trans
  rw [lintegral_lintegral_swap
    (stoppingGreen_joint_measurable hBm hc κ γ G F hw S hS.measurable').ennreal_ofReal.aemeasurable]
  exact setLIntegral_mono' hAI (fun z hz =>
    stoppingGreen_mean_le hB hBm hc hB0 hκ hκ8 γ G F hw z (hAH hz) S hS)

theorem stoppingCurrentGreen_spatial_mean_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {B : ℝ≥0 → Ω → ℝ} (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ : ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (S : Ω → ℝ≥0∞) (hS : Measurable S) (K : Set ℂ)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) (E : Set Ω) :
    Tendsto (fun n => ∫⁻ ω in E, (∫⁻ z in K,
      f z * ENNReal.ofReal (levelStoppingCurrentGreen κ B γ G (u n) S z ω) ∂volume) ∂P)
      atTop (𝓝 (∫⁻ ω in E, (∫⁻ z in K, f z * ENNReal.ofReal
        (stoppingGreen κ B γ G S z ω) ∂volume) ∂P)) := by
  let a (n : ℕ) (q : Ω × ℂ) :=
    f q.2 * ENNReal.ofReal (levelStoppingCurrentGreen κ B γ G (u n) S q.2 q.1)
  have ha (n : ℕ) : Measurable (a n) :=
    (hf.comp measurable_snd).mul
      (levelStoppingCurrentGreen_joint_measurable hBm hBc κ (u n) (hu n) γ G F hw S hS).ennreal_ofReal
  have ham (ω : Ω) : Monotone (fun n => fun z => a n (ω,z)) := by
    intro n m hnm z
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
      (levelStoppingCurrentGreen_mono ω (hBc ω) (hw ω) z S (hu n) (hmono hnm)))
  have hal (ω : Ω) : Tendsto (fun n => ∫⁻ z in K, a n (ω,z)) atTop
      (𝓝 (∫⁻ z in K, f z * ENNReal.ofReal
        (stoppingGreen κ B γ G S z ω))) := by
    apply lintegral_tendsto_of_tendsto_of_monotone (μ := volume.restrict K)
      (f := fun n z => a n (ω,z))
      (fun n => ((ha n).comp (measurable_const.prodMk measurable_id)).aemeasurable)
      (Eventually.of_forall (fun z n m hnm => ham ω hnm z))
    filter_upwards [] with z
    apply tendsto_const_nhds.congr'
    exact (levelStoppingCurrentGreen_eventually_eq ω (hBc ω) (hw ω) z S u hu hlim).mono
      (fun n hn => congrArg (fun x : ℝ => f z * ENNReal.ofReal x) hn.symm)
  exact lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (ha n).lintegral_prod_right'.aemeasurable)
    (Eventually.of_forall (fun ω n m hnm => lintegral_mono (ham ω hnm)))
    (Eventually.of_forall hal)

theorem halfPlaneStoppingCurrentMeasure_mean_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {B : ℝ≥0 → Ω → ℝ} (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ : ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (S : Ω → ℝ≥0∞) (hS : Measurable S) (E : Set Ω)
    (A : Set upperHalfPlane) (hA : MeasurableSet A) :
    Tendsto (fun n => (P.restrict E).bind (halfPlaneStoppingCurrentMeasure κ B γ G (u n) S) A)
      atTop (𝓝 ((P.restrict E).bind (halfPlaneStoppingGreenMeasure κ B γ G S) A)) := by
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [Measure.bind_apply hA
    (halfPlaneStoppingCurrentMeasure_measurable hBm hBc κ (u _) (hu _) γ G F hw S hS).aemeasurable,
    Measure.bind_apply hA (halfPlaneStoppingGreenMeasure_measurable hBm hBc κ γ G F hw S hS).aemeasurable,
    halfPlaneStoppingCurrentMeasure,halfPlaneStoppingGreenMeasure,
    comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,withDensity_apply _ hAI]
  simpa only [one_mul] using stoppingCurrentGreen_spatial_mean_tendsto P hBm hBc κ γ G F hw
    u hu hmono hlim S hS _ (fun _ => 1) measurable_const E

end SLEExactGauge.Multipoint

end

end OAI
