import OAI.Probability.SLE.Mass.LevelRandomRadon
import OAI.Probability.SLE.Mass.ConvexMomentLimits

namespace OAI

/-! Every compact moment bound passes from the actual level measures to
any of their common convex Radon limits. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma extendHalfPlaneTest_nonneg (f : upperHalfPlane → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∀ z, 0 ≤ extendHalfPlaneTest f z := by
  intro z
  by_cases hz : z ∈ upperHalfPlane
  · exact (extendHalfPlaneTest_apply f ⟨z,hz⟩).symm ▸ hf ⟨z,hz⟩
  · rw [extendHalfPlaneTest_of_not_mem f z hz]

lemma ofReal_integral_halfPlaneLevelMeasure
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (ω : Ω) (hBc : Continuous (fun t => B t ω))
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (t : ℝ≥0∞) (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) :
    ENNReal.ofReal (∫ z, f z ∂halfPlaneLevelMeasure κ B γ G u t ω) =
      levelApproximationTest κ B γ G u t (fun z => ENNReal.ofReal (extendHalfPlaneTest f z)) ω := by
  let K := (Subtype.val : upperHalfPlane → ℂ) '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image continuous_subtype_val
  have hKH : K ⊆ upperHalfPlane := by rintro _ ⟨x,_,rfl⟩; exact x.property
  have hfin := (levelApproximation_apply_le κ B γ G u t ω hK.measurableSet).trans_lt
    (levelMass_lt_top_of_compact hκ hκ8 γ G F ω hBc hw K hK hKH u)
  rw [integral_halfPlaneLevelMeasure]
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_of_bounded_support _ K hK.measurableSet hfin _
      (extendHalfPlaneTest_measurable f f.continuous.measurable) _
      (fun z _ => extendHalfPlaneTest_norm_le f z) (extendHalfPlaneTest_support f))
    (Eventually.of_forall (extendHalfPlaneTest_nonneg f hf))

theorem uniform_halfPlaneLevelMeasure_test_moments
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) (m : ℕ) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ u : ℝ, 0 ≤ u → ∀ t : ℝ≥0∞,
      (∫⁻ ω, ENNReal.ofReal (∫ z, f z ∂halfPlaneLevelMeasure κ B γ G u t ω)^m ∂P) ≤ M := by
  let K := (Subtype.val : upperHalfPlane → ℂ) '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image continuous_subtype_val
  have hKH : K ⊆ upperHalfPlane := by rintro _ ⟨x,_,rfl⟩; exact x.property
  obtain ⟨M,hM,hbound⟩ := uniform_levelApproximationTest_moments hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth K hK hKH (fun z => ENNReal.ofReal (extendHalfPlaneTest f z))
    (ENNReal.ofReal ‖f.toBoundedContinuousFunction‖) ENNReal.ofReal_lt_top
    (fun z _ => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (extendHalfPlaneTest_norm_le f z)))
    (fun z hz => by rw [extendHalfPlaneTest_support f z hz,ENNReal.ofReal_zero]) m
  refine ⟨M,hM,fun u hu t => ?_⟩
  simpa only [ofReal_integral_halfPlaneLevelMeasure hκ hκ8 γ G F _ (hBc _) (hw _) u t f hf]
    using hbound u hu t

theorem uniform_convexLevelMeasure_test_moments
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) (m : ℕ) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n (t : ℝ≥0∞),
      (∫⁻ ω, ENNReal.ofReal (∫ z, f z ∂convexLevelMeasure κ B γ G u s w n t ω)^m ∂P) ≤ M := by
  obtain ⟨M,hM,hbound⟩ := uniform_halfPlaneLevelMeasure_test_moments hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth f hf m
  refine ⟨M,hM,fun n t => ?_⟩
  have hb := lintegral_pow_convex_sum_le P (s n) (w n)
    (fun i ω => ∫ z, f z ∂halfPlaneLevelMeasure κ B γ G (u (n+i)) t ω)
    (hw₀ n) (hw₁ n) (fun i _ ω => integral_nonneg hf)
    (fun i _ => by
      simp_rw [integral_halfPlaneLevelMeasure]
      exact levelApproximationRealTest_measurable hm hBc κ (u (n+i)) (hu _) γ G F hw t
        _ (extendHalfPlaneTest_measurable f f.continuous.measurable))
    m M (fun i _ => hbound (u (n+i)) (hu _) t)
  simpa only [integral_convexLevelMeasure hκ hκ8 γ G F _ (hBc _) (hw _) u s w n t (hw₀ n) f,
    integral_halfPlaneLevelMeasure] using hb

theorem level_radon_limit_test_moments
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (t : ℝ≥0∞) (ν : Ω → Measure upperHalfPlane)
    (hlim : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n t ω)
        atTop (𝓝 (∫ z, f z ∂ν ω)))
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) (m : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (∫ z, f z ∂ν ω)^m ∂P) < ⊤ := by
  obtain ⟨M,hM,hbound⟩ := uniform_convexLevelMeasure_test_moments hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth u hu s w hw₀ hw₁ f hf m
  apply lt_of_le_of_lt (lintegral_le_of_ae_tendsto_bound P _ _ (fun n =>
    ((convexLevelMeasure_test_measurable hm hBc hκ hκ8 γ G F hw u hu s w hw₀ n t f).ennreal_ofReal.pow_const m).aemeasurable)
    ?_ M (fun n => hbound n t)) hM
  filter_upwards [hlim] with ω hω
  exact (ENNReal.continuous_pow m).continuousAt.tendsto.comp
    ((ENNReal.continuous_ofReal.tendsto _).comp (hω f))

lemma measure_compact_le_nonneg_test (ν : Measure upperHalfPlane)
    [IsFiniteMeasureOnCompacts ν] (K : Set upperHalfPlane) (hK : IsCompact K)
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) (hKf : ∀ z ∈ K, 1 ≤ f z) :
    ν K ≤ ENNReal.ofReal (∫ z, f z ∂ν) := by
  rw [ofReal_integral_eq_lintegral_ofReal f.integrable (Eventually.of_forall hf)]
  calc
    _ = ∫⁻ z, K.indicator (fun _ => (1 : ℝ≥0∞)) z ∂ν := by
      rw [lintegral_indicator_const hK.measurableSet,one_mul]
    _ ≤ _ := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ K
      · simpa only [indicator_of_mem hz,ENNReal.one_le_ofReal] using hKf z hz
      · simp only [indicator_of_notMem hz,zero_le]

theorem level_radon_limit_compact_moments
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (t : ℝ≥0∞) (ν : Ω → Measure upperHalfPlane)
    (hν : ∀ ω, IsFiniteMeasureOnCompacts (ν ω))
    (hlim : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n t ω)
        atTop (𝓝 (∫ z, f z ∂ν ω)))
    (K : Set upperHalfPlane) (hK : IsCompact K) (m : ℕ) :
    (∫⁻ ω, (ν ω K)^m ∂P) < ⊤ := by
  obtain ⟨f,hf,hKf⟩ := exists_compact_test_cutoff K hK
  apply lt_of_le_of_lt (lintegral_mono (fun ω => ?_))
    (level_radon_limit_test_moments hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth
      u hu s w hw₀ hw₁ t ν hlim f hf m)
  let := hν ω
  exact pow_le_pow_left' (measure_compact_le_nonneg_test (ν ω) K hK f hf hKf) m

end SLEExactGauge.Multipoint

end

end OAI
