import OAI.Probability.SLE.Mass.LevelStoppingMeasures
import OAI.Probability.SLE.Mass.LevelCurrentTests
import OAI.Probability.SLE.Mass.LevelConditionalMean

namespace OAI

/-! Signed compact-test convergence for the Green remainder at arbitrary
stopping times, and its preservation by the chosen convex tails. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma levelStoppingCurrentGreen_le_green
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hw : IsCapacityTwoWitness
      (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (S : Ω → ℝ≥0∞) (z : ℂ) :
    levelStoppingCurrentGreen κ B γ G u S z ω ≤ stoppingGreen κ B γ G S z ω := by
  by_cases hfin : S ω < ∞
  · unfold levelStoppingCurrentGreen stoppingGreen
    rw [ite_eq_left hfin]
    split_ifs
    · exact le_rfl
    · exact greenDensity_nonneg hw κ _ z
  · have hnot : ¬ S ω < radiusLevelTime (γ ω) (G ω) z u :=
      fun h => hfin (h.trans_le le_top)
    simp only [levelStoppingCurrentGreen,stoppingGreen,ite_eq_right hfin,ite_eq_right hnot]
    exact le_rfl

lemma halfPlaneStoppingCurrentMeasure_le_green
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hw : IsCapacityTwoWitness
      (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (S : Ω → ℝ≥0∞) :
    halfPlaneStoppingCurrentMeasure κ B γ G u S ω ≤ halfPlaneStoppingGreenMeasure κ B γ G S ω := by
  apply Measure.le_iff.mpr
  intro A hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  simp only [halfPlaneStoppingCurrentMeasure,halfPlaneStoppingGreenMeasure,
    comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,withDensity_apply _ hAI]
  exact lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (levelStoppingCurrentGreen_le_green ω hw u S z))

lemma halfPlaneStoppingCurrentMeasure_mean_lintegral_test
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {B : ℝ≥0 → Ω → ℝ} (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (S : Ω → ℝ≥0∞) (hS : Measurable S) (f : upperHalfPlane → ℝ) (hf : Measurable f) :
    (∫⁻ z, ENNReal.ofReal (f z) ∂P.bind (halfPlaneStoppingCurrentMeasure κ B γ G u S)) =
      ∫⁻ ω, (∫⁻ z, ENNReal.ofReal (extendHalfPlaneTest f z) *
        ENNReal.ofReal (levelStoppingCurrentGreen κ B γ G u S z ω) ∂volume) ∂P :=
  lintegral_density_kernel_test P _
    (halfPlaneStoppingCurrentMeasure_measurable hBm hBc κ u hu γ G F hw S hS) _
    (levelStoppingCurrentGreen_joint_measurable hBm hBc κ u hu γ G F hw S hS).ennreal_ofReal
    (fun _ => rfl) f hf

lemma halfPlaneStoppingGreenMeasure_mean_lintegral_test
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {B : ℝ≥0 → Ω → ℝ} (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ : ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (S : Ω → ℝ≥0∞) (hS : Measurable S) (f : upperHalfPlane → ℝ) (hf : Measurable f) :
    (∫⁻ z, ENNReal.ofReal (f z) ∂P.bind (halfPlaneStoppingGreenMeasure κ B γ G S)) =
      ∫⁻ ω, (∫⁻ z, ENNReal.ofReal (extendHalfPlaneTest f z) * ENNReal.ofReal
        (stoppingGreen κ B γ G S z ω) ∂volume) ∂P :=
  lintegral_density_kernel_test P _ (halfPlaneStoppingGreenMeasure_measurable hBm hBc κ γ G F hw S hS) _
    (stoppingGreen_joint_measurable hBm hBc κ γ G F hw S hS).ennreal_ofReal
    (fun _ => rfl) f hf

lemma halfPlaneStoppingCurrentMeasure_mean_lintegral_test_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {B : ℝ≥0 → Ω → ℝ} (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ : ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (S : Ω → ℝ≥0∞) (hS : Measurable S) (E : Set Ω)
    (f : upperHalfPlane → ℝ) (hf : Measurable f) :
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (f z)
      ∂(P.restrict E).bind (halfPlaneStoppingCurrentMeasure κ B γ G (u n) S)) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (f z) ∂(P.restrict E).bind (halfPlaneStoppingGreenMeasure κ B γ G S))) := by
  simp_rw [halfPlaneStoppingCurrentMeasure_mean_lintegral_test _ hBm hBc κ _ (hu _) γ G F hw S hS f hf,
    halfPlaneStoppingGreenMeasure_mean_lintegral_test _ hBm hBc κ γ G F hw S hS f hf]
  simpa only [Measure.restrict_univ] using stoppingCurrentGreen_spatial_mean_tendsto P hBm hBc κ γ G F hw
    u hu hmono hlim S hS univ (fun z => ENNReal.ofReal (extendHalfPlaneTest f z))
    (extendHalfPlaneTest_measurable f hf).ennreal_ofReal E

lemma halfPlaneStoppingCurrentMeasure_mean_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : 0 ≤ u) (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) S)
    (E : Set Ω) :
    (P.restrict E).bind (halfPlaneStoppingCurrentMeasure κ B γ G u S) ≤ initialGreenMeasure κ := by
  apply le_trans ?_ (halfPlaneStoppingGreenMeasure_mean_le hB hBm hBc hB0 hκ hκ8 γ G F hw S hS E)
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA (halfPlaneStoppingCurrentMeasure_measurable hBm hBc κ u hu γ G F hw S hS.measurable').aemeasurable,
    Measure.bind_apply hA (halfPlaneStoppingGreenMeasure_measurable hBm hBc κ γ G F hw S hS.measurable').aemeasurable]
  exact lintegral_mono (fun ω => halfPlaneStoppingCurrentMeasure_le_green ω (hw ω) u S A)

theorem halfPlaneStoppingCurrentMeasure_mean_test_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) S)
    (E : Set Ω)
    (f : C_c(upperHalfPlane,ℝ)) :
    Tendsto (fun n => ∫ z, f z ∂(P.restrict E).bind (halfPlaneStoppingCurrentMeasure κ B γ G (u n) S))
      atTop (𝓝 (∫ z, f z ∂(P.restrict E).bind (halfPlaneStoppingGreenMeasure κ B γ G S))) := by
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  have hfi : Integrable f (initialGreenMeasure κ) := f.integrable
  apply integral_tendsto_of_lintegral_pos_neg
  · exact fun n => hfi.mono_measure (halfPlaneStoppingCurrentMeasure_mean_le hB hBm hBc hB0 hκ hκ8
      γ G F hw (u n) (hu n) S hS E)
  · exact hfi.mono_measure (halfPlaneStoppingGreenMeasure_mean_le hB hBm hBc hB0 hκ hκ8 γ G F hw S hS E)
  · exact halfPlaneStoppingCurrentMeasure_mean_lintegral_test_tendsto P hBm hBc κ γ G F hw
      u hu hmono hlim S hS.measurable' E f f.continuous.measurable
  · exact halfPlaneStoppingCurrentMeasure_mean_lintegral_test_tendsto P hBm hBc κ γ G F hw
      u hu hmono hlim S hS.measurable' E (fun z => -f z) f.continuous.measurable.neg

end SLEExactGauge.Multipoint

end

end OAI
