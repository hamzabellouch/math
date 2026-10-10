import OAI.Probability.SLE.Mass.LevelStoppingKernel

namespace OAI

/-! Joint spatial measurability and the spatial form of the finite-level
conditional kernel at an arbitrary, possibly infinite, stopping time. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

lemma actual_greenDensity_random_time_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : Measurable (Function.uncurry B)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (t : Ω → ℝ≥0) (ht : Measurable t) :
    Measurable (fun p : Ω × ℂ => greenDensity κ
      (fun s => Real.sqrt κ * B s p.1) (γ p.1) (G p.1) (t p.1) p.2) := by
  let U (s : ℝ≥0) (ω : Ω) := Real.sqrt κ * B s ω
  let c := spatialClippedFamily U (hBm.const_mul _) (fun ω => (hc ω).const_mul _)
  have hmap : Measurable (fun p : Ω × ℂ => (t p.1,p.2,p.1)) :=
    (ht.comp measurable_fst).prodMk (measurable_snd.prodMk measurable_fst)
  have hj := (c.jointGreen_measurable κ B hBm).comp hmap
  have he (p : Ω × ℂ) : c.jointGreen κ B (t p.1,p.2,p.1) =
      greenDensity κ (fun s => Real.sqrt κ * B s p.1) (γ p.1) (G p.1) (t p.1) p.2 :=
    c.jointGreen_eq κ B p.1 ((hc p.1).const_mul _) (fun _ => rfl) (hw p.1) _ _
  simpa only [Function.comp_def,he] using hj

lemma levelStoppingRemainderGreen_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (S : Ω → ℝ≥0∞) (hS : Measurable S) :
    Measurable (fun p : Ω × ℂ => levelStoppingRemainderGreen κ B γ G u S p.2 p.1) :=
  Measurable.ite
    (measurableSet_lt (hS.comp measurable_fst)
      (actual_radiusLevel_joint_measurable hm hc κ u hu γ G F hw))
    (actual_stoppedGreen_joint_measurable hm hc κ u hu γ G F hw) measurable_const

lemma levelStoppingCurrentGreen_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hBm : Measurable (Function.uncurry B)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (S : Ω → ℝ≥0∞) (hS : Measurable S) :
    Measurable (fun p : Ω × ℂ => levelStoppingCurrentGreen κ B γ G u S p.2 p.1) := by
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  exact Measurable.ite
    (measurableSet_lt (hS.comp measurable_fst)
      (actual_radiusLevel_joint_measurable hm hc κ u hu γ G F hw))
    (actual_greenDensity_random_time_joint_measurable hBm hc κ γ G F hw
      (fun ω => (S ω).toNNReal) (ENNReal.measurable_toNNReal.comp hS)) measurable_const

theorem levelStoppingRemainderGreen_spatial_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : 0 ≤ u) (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) S)
    (K : Set ℂ) (hK : MeasurableSet K) (hKH : K ⊆ upperHalfPlane)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) (E : Set Ω)
    (hE : MeasurableSet[hS.measurableSpace] E) :
    (∫⁻ ω in E, (∫⁻ z in K, f z * ENNReal.ofReal
      (levelStoppingRemainderGreen κ B γ G u S z ω) ∂volume) ∂P) =
      ∫⁻ ω in E, (∫⁻ z in K, f z * ENNReal.ofReal
        (levelStoppingCurrentGreen κ B γ G u S z ω) ∂volume) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  have hmR := levelStoppingRemainderGreen_joint_measurable hm hc κ u hu γ G F hw S hS.measurable'
  have hmC := levelStoppingCurrentGreen_joint_measurable hBm hc κ u hu γ G F hw S hS.measurable'
  have hR := (hf.comp measurable_snd).mul hmR.ennreal_ofReal
  have hC := (hf.comp measurable_snd).mul hmC.ennreal_ofReal
  conv_lhs => rw [lintegral_lintegral_swap hR.aemeasurable]
  conv_rhs => rw [lintegral_lintegral_swap hC.aemeasurable]
  apply setLIntegral_congr_fun hK
  intro z hz
  dsimp only
  have hp : Measurable (fun ω : Ω => (ω,z)) := measurable_id.prodMk measurable_const
  have hRz := hmR.ennreal_ofReal.comp hp
  have hCz := hmC.ennreal_ofReal.comp hp
  simp only [Function.comp_def] at hRz hCz
  rw [lintegral_const_mul _ hRz,lintegral_const_mul _ hCz]
  rw [levelStoppingRemainderGreen_setLIntegral hB hBm hc hB0 hκ hκ8
    γ G F hw z (hKH hz) u hu S hS E hE]

lemma stopping_level_density_split
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (S : Ω → ℝ≥0∞) (ω : Ω) (z : ℂ) :
    levelApproximationDensity κ B γ G u ∞ ω z =
      levelApproximationDensity κ B γ G u (S ω) ω z +
        ENNReal.ofReal (levelStoppingRemainderGreen κ B γ G u S z ω) := by
  by_cases h : radiusLevelTime (γ ω) (G ω) z u ≤ S ω
  · simp only [levelApproximationDensity,le_top,ite_true,ite_eq_left h,
      levelStoppingRemainderGreen,ite_eq_right (not_lt.mpr h),ENNReal.ofReal_zero,add_zero]
  · simp only [levelApproximationDensity,le_top,ite_true,ite_eq_right h,
      levelStoppingRemainderGreen,ite_eq_left (lt_of_not_ge h),zero_add]

end SLEExactGauge.Multipoint

end

end OAI
