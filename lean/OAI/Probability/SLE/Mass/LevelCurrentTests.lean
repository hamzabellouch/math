import OAI.Probability.SLE.Mass.LevelCurrentLimit
import OAI.Probability.SLE.Mass.SignedMeasureConvergence

namespace OAI

/-! Signed compact tests of the current Green mean pass through the
increasing radius levels. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma lintegral_halfPlane_density_test (ρ : ℂ → ℝ≥0∞) (hρ : Measurable ρ)
    (f : upperHalfPlane → ℝ) (hf : Measurable f) :
    (∫⁻ z : upperHalfPlane, ENNReal.ofReal (f z)
      ∂(volume.withDensity ρ).comap Subtype.val) =
      ∫⁻ z, ENNReal.ofReal (extendHalfPlaneTest f z) * ρ z ∂volume := by
  calc
    _ = ∫⁻ z : upperHalfPlane, ENNReal.ofReal (extendHalfPlaneTest f z)
        ∂(volume.withDensity ρ).comap Subtype.val := by
      congr 1
      funext z
      rw [extendHalfPlaneTest_apply]
    _ = ∫⁻ z in upperHalfPlane, ENNReal.ofReal (extendHalfPlaneTest f z)
        ∂volume.withDensity ρ :=
      lintegral_subtype_comap (μ := volume.withDensity ρ) isOpen_upperHalfPlane.measurableSet
        (fun z => ENNReal.ofReal (extendHalfPlaneTest f z))
    _ = ∫⁻ z, ENNReal.ofReal (extendHalfPlaneTest f z) ∂volume.withDensity ρ := by
      apply setLIntegral_eq_of_support_subset
      intro z hz
      by_contra hn
      exact hz (by
        dsimp only
        rw [extendHalfPlaneTest_of_not_mem f z hn,ENNReal.ofReal_zero])
    _ = _ := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hρ
        (extendHalfPlaneTest_measurable f hf).ennreal_ofReal]
      apply lintegral_congr
      intro z
      exact mul_comm _ _

lemma lintegral_density_kernel_test
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ)
    (ρ : Ω × ℂ → ℝ≥0∞) (hρ : Measurable ρ)
    (he : ∀ ω, μ ω = (volume.withDensity (fun z => ρ (ω,z))).comap Subtype.val)
    (f : upperHalfPlane → ℝ) (hf : Measurable f) :
    (∫⁻ z, ENNReal.ofReal (f z) ∂P.bind μ) =
      ∫⁻ ω, (∫⁻ z, ENNReal.ofReal (extendHalfPlaneTest f z) * ρ (ω,z) ∂volume) ∂P := by
  rw [Measure.lintegral_bind hμ.aemeasurable hf.ennreal_ofReal.aemeasurable]
  apply lintegral_congr
  intro ω
  rw [he ω]
  exact lintegral_halfPlane_density_test _
    (hρ.comp (measurable_const.prodMk measurable_id)) f hf

lemma halfPlaneCurrentMeasure_mean_lintegral_test
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {B : ℝ≥0 → Ω → ℝ} (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) (f : upperHalfPlane → ℝ) (hf : Measurable f) :
    (∫⁻ z, ENNReal.ofReal (f z) ∂P.bind (halfPlaneCurrentMeasure κ B γ G u t)) =
      ∫⁻ ω, (∫⁻ z, ENNReal.ofReal (extendHalfPlaneTest f z) *
        ENNReal.ofReal (levelCurrentGreen κ B γ G u t z ω) ∂volume) ∂P :=
  lintegral_density_kernel_test P _
    (halfPlaneCurrentMeasure_measurable hBm hBc κ u hu γ G F hw t) _
    (levelCurrentGreen_joint_measurable hBm hBc κ u hu γ G F hw t).ennreal_ofReal
    (fun _ => rfl) f hf

lemma halfPlaneGreenMeasure_mean_lintegral_test
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {B : ℝ≥0 → Ω → ℝ} (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ : ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) (f : upperHalfPlane → ℝ) (hf : Measurable f) :
    (∫⁻ z, ENNReal.ofReal (f z) ∂P.bind (halfPlaneGreenMeasure κ B γ G t)) =
      ∫⁻ ω, (∫⁻ z, ENNReal.ofReal (extendHalfPlaneTest f z) * ENNReal.ofReal
        (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z) ∂volume) ∂P :=
  lintegral_density_kernel_test P _ (halfPlaneGreenMeasure_measurable hBm hBc κ γ G F hw t) _
    (actual_greenDensity_joint_measurable hBm hBc κ γ G F hw t).ennreal_ofReal
    (fun _ => rfl) f hf

lemma halfPlaneCurrentMeasure_mean_lintegral_test_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {B : ℝ≥0 → Ω → ℝ} (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ : ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (t : ℝ≥0) (E : Set Ω)
    (f : upperHalfPlane → ℝ) (hf : Measurable f) :
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (f z)
      ∂(P.restrict E).bind (halfPlaneCurrentMeasure κ B γ G (u n) t)) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (f z) ∂(P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t))) := by
  simp_rw [halfPlaneCurrentMeasure_mean_lintegral_test _ hBm hBc κ _ (hu _) γ G F hw t f hf,
    halfPlaneGreenMeasure_mean_lintegral_test _ hBm hBc κ γ G F hw t f hf]
  simpa only [Measure.restrict_univ] using currentGreen_spatial_mean_tendsto P hBm hBc κ γ G F hw
    u hu hmono hlim t univ (fun z => ENNReal.ofReal (extendHalfPlaneTest f z))
    (extendHalfPlaneTest_measurable f hf).ennreal_ofReal E

lemma halfPlaneCurrentMeasure_mean_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0) (E : Set Ω) :
    (P.restrict E).bind (halfPlaneCurrentMeasure κ B γ G u t) ≤ initialGreenMeasure κ := by
  apply le_trans ?_ (halfPlaneGreenMeasure_mean_le hB hBm hBc hB0 hκ hκ8 γ G F hw t E)
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA (halfPlaneCurrentMeasure_measurable hBm hBc κ u hu γ G F hw t).aemeasurable,
    Measure.bind_apply hA (halfPlaneGreenMeasure_measurable hBm hBc κ γ G F hw t).aemeasurable]
  exact lintegral_mono (fun ω => halfPlaneCurrentMeasure_le_green ω (hw ω) u t A)

theorem halfPlaneCurrentMeasure_mean_test_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u)
    (hlim : Tendsto u atTop atTop) (t : ℝ≥0) (E : Set Ω)
    (f : C_c(upperHalfPlane,ℝ)) :
    Tendsto (fun n => ∫ z, f z ∂(P.restrict E).bind (halfPlaneCurrentMeasure κ B γ G (u n) t))
      atTop (𝓝 (∫ z, f z ∂(P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t))) := by
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  have hfi : Integrable f (initialGreenMeasure κ) := f.integrable
  apply integral_tendsto_of_lintegral_pos_neg
  · exact fun n => hfi.mono_measure (halfPlaneCurrentMeasure_mean_le hB hBm hBc hB0 hκ hκ8
      γ G F hw (u n) (hu n) t E)
  · exact hfi.mono_measure (halfPlaneGreenMeasure_mean_le hB hBm hBc hB0 hκ hκ8 γ G F hw t E)
  · exact halfPlaneCurrentMeasure_mean_lintegral_test_tendsto P hBm hBc κ γ G F hw
      u hu hmono hlim t E f f.continuous.measurable
  · exact halfPlaneCurrentMeasure_mean_lintegral_test_tendsto P hBm hBc κ γ G F hw
      u hu hmono hlim t E (fun z => -f z) f.continuous.measurable.neg

end SLEExactGauge.Multipoint

end

end OAI
