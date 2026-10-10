import OAI.Probability.SLE.Mass.LevelRadonMoments
import OAI.Probability.SLE.Gauge.WeightedMomentIntegration

namespace OAI

/-! The actual multipoint estimate with spatial weights retained. This
retains the near-diagonal gain needed for nonatomicity. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

def weightedLevelMass {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (K : Set ℂ) (f : ℂ → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ z in K, f z * ENNReal.ofReal (stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
    (γ ω) (G ω) z u)

theorem weightedLevelMass_moment_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SigmaFinite P]
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (K : Set ℂ) (f : ℂ → ℝ≥0∞) (hf : Measurable f) (m : ℕ) :
    (∫⁻ ω, weightedLevelMass κ B γ G u K f ω ^ m ∂P) =
      ∫⁻ z : Fin m → ℂ, (∏ i, f (z i)) *
        (∫⁻ ω, ENNReal.ofReal (∏ i, stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
          (γ ω) (G ω) (z i) u) ∂P) ∂Measure.pi (fun _ : Fin m => volume.restrict K) := by
  have hW := (actual_stoppedGreen_joint_measurable hm hBc κ u hu γ G F hw).ennreal_ofReal
  unfold weightedLevelMass
  rw [lintegral_weighted_mass_pow_eq P (volume.restrict K)
    (fun ω z => ENNReal.ofReal (stoppedGreen κ
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u)) hW f hf m]
  apply lintegral_congr
  intro z
  apply congrArg (fun v : ℝ≥0∞ => (∏ i, f (z i)) * v)
  apply lintegral_congr
  intro ω
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => stoppedGreen_nonneg (hw ω) κ _ _)).symm

theorem actual_product_le_cappedKernel
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    {m : ℕ} (z : Fin m → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane) (hzi : Function.Injective z)
    (b : ℝ) (hb : 0 < b) (hbR : ∀ i, b ≤ 2*(z i).im) (u : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (∏ i, stoppedGreen κ
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (z i) u) ∂P) ≤
      ENNReal.ofReal (multipointConstant κ m) * cappedDistanceKernel (codimension κ) b z := by
  have hc := stoppedGreen_common_level_product_bound hB hm hBm hBc hB0 hκ hκ8 γ G F hw
    hgrowth z hz hzi (cappedDistance b z) (fun i => cap_pos hb hzi i)
    (fun i => (cap_le_fixed b z i).trans (hbR i))
    (fun i j hij => cap_le_dist b z i j hij) u
  apply hc.trans_eq
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1
  · simp only [multipointConstant,Fintype.card_fin]
  · exact ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Real.rpow_nonneg (cap_pos hb hzi i).le _)

theorem weightedLevelMass_moment_le_cappedKernel
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (K : Set ℂ) (hK : MeasurableSet K) (hKH : K ⊆ upperHalfPlane)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f)
    (b : ℝ) (hb : 0 < b) (hbR : ∀ z ∈ K, b ≤ 2*z.im) (m : ℕ)
    (u : ℝ) (hu : 0 ≤ u) :
    (∫⁻ ω, weightedLevelMass κ B γ G u K f ω ^ m ∂P) ≤
      ENNReal.ofReal (multipointConstant κ m) *
        ∫⁻ z : Fin m → ℂ, (∏ i, f (z i)) * cappedDistanceKernel (codimension κ) b z
          ∂Measure.pi (fun _ : Fin m => volume.restrict K) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [weightedLevelMass_moment_identity P hm hBc κ u hu γ G F hw K f hf m]
  have hk : Measurable (fun z : Fin m → ℂ =>
      (∏ i, f (z i)) * cappedDistanceKernel (codimension κ) b z) :=
    (Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))).mul
      (measurable_cappedDistanceKernel _ _)
  rw [← lintegral_const_mul _ hk]
  apply lintegral_mono_ae
  filter_upwards [ae_tuple_mem (ι := Fin m) K hK,ae_tuple_injective (ι := Fin m) K] with z hz hzi
  have he := actual_product_le_cappedKernel hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth
    z (fun i => hKH (hz i)) hzi b hb (fun i => hbR (z i) (hz i)) u
  exact (mul_le_mul' le_rfl he).trans_eq (by ac_rfl)

lemma levelApproximationTest_le_weightedLevelMass
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (K : Set ℂ) (hK : MeasurableSet K) (f : ℂ → ℝ≥0∞) (hf : Measurable f)
    (hz : ∀ z ∉ K, f z = 0) (t : ℝ≥0∞) (ω : Ω) :
    levelApproximationTest κ B γ G u t f ω ≤ weightedLevelMass κ B γ G u K f ω := by
  have hd := levelApproximationDensity_joint_measurable hm hBc κ u hu γ G F hw t
  change (∫⁻ z, f z ∂volume.withDensity _) ≤ _
  rw [lintegral_withDensity_eq_lintegral_mul volume hd.of_uncurry_left hf]
  have he : (fun z => levelApproximationDensity κ B γ G u t ω z * f z) =
      K.indicator (fun z => levelApproximationDensity κ B γ G u t ω z * f z) := by
    funext z
    by_cases hzK : z ∈ K
    · simp only [indicator_of_mem hzK]
    · simp only [indicator_of_notMem hzK,hz z hzK,mul_zero]
  change (∫⁻ z, levelApproximationDensity κ B γ G u t ω z * f z) ≤ _
  rw [he,lintegral_indicator hK]
  apply lintegral_mono
  intro z
  unfold levelApproximationDensity
  dsimp only
  split_ifs
  · exact (mul_comm _ _).le
  · simp only [zero_mul,zero_le]

theorem levelApproximationTest_moment_le_cappedKernel
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (K : Set ℂ) (hK : MeasurableSet K) (hKH : K ⊆ upperHalfPlane)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) (hz : ∀ z ∉ K, f z = 0)
    (b : ℝ) (hb : 0 < b) (hbR : ∀ z ∈ K, b ≤ 2*z.im) (m : ℕ)
    (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0∞) :
    (∫⁻ ω, levelApproximationTest κ B γ G u t f ω ^ m ∂P) ≤
      ENNReal.ofReal (multipointConstant κ m) *
        ∫⁻ z : Fin m → ℂ, (∏ i, f (z i)) * cappedDistanceKernel (codimension κ) b z
          ∂Measure.pi (fun _ : Fin m => volume.restrict K) := by
  apply (lintegral_mono (fun ω => pow_le_pow_left'
    (levelApproximationTest_le_weightedLevelMass hm hBc κ u hu γ G F hw K hK f hf hz t ω) m)).trans
  exact weightedLevelMass_moment_le_cappedKernel hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth
    K hK hKH f hf b hb hbR m u hu

theorem level_radon_limit_test_moment_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (t : ℝ≥0∞) (ν : Ω → Measure upperHalfPlane)
    (hlim : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n t ω)
        atTop (𝓝 (∫ z, f z ∂ν ω)))
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) (m : ℕ) (M : ℝ≥0∞)
    (hbound : ∀ n, (∫⁻ ω, ENNReal.ofReal
      (∫ z, f z ∂halfPlaneLevelMeasure κ B γ G (u n) t ω)^m ∂P) ≤ M) :
    (∫⁻ ω, ENNReal.ofReal (∫ z, f z ∂ν ω)^m ∂P) ≤ M := by
  apply lintegral_le_of_ae_tendsto_bound P
    (fun n ω => ENNReal.ofReal (∫ z, f z ∂convexLevelMeasure κ B γ G u s w n t ω)^m)
    (fun ω => ENNReal.ofReal (∫ z, f z ∂ν ω)^m)
    (fun n => ((convexLevelMeasure_test_measurable hm hBc hκ hκ8 γ G F hw u hu s w hw₀ n t f).ennreal_ofReal.pow_const m).aemeasurable)
  · filter_upwards [hlim] with ω hω
    exact (ENNReal.continuous_pow m).continuousAt.tendsto.comp
      ((ENNReal.continuous_ofReal.tendsto _).comp (hω f))
  · intro n
    have hb := lintegral_pow_convex_sum_le P (s n) (w n)
      (fun i ω => ∫ z, f z ∂halfPlaneLevelMeasure κ B γ G (u (n+i)) t ω)
      (hw₀ n) (hw₁ n) (fun i _ ω => integral_nonneg hf)
      (fun i _ => by
        simp_rw [integral_halfPlaneLevelMeasure]
        exact levelApproximationRealTest_measurable hm hBc κ (u (n+i)) (hu _) γ G F hw t
          _ (extendHalfPlaneTest_measurable f f.continuous.measurable))
      m M (fun i _ => hbound (n+i))
    simpa only [integral_convexLevelMeasure hκ hκ8 γ G F _ (hBc _) (hw _) u s w n t (hw₀ n) f,
      integral_halfPlaneLevelMeasure] using hb

end SLEExactGauge.Multipoint

end

end OAI
