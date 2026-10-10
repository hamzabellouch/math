import OAI.Probability.SLE.Mass.LevelStoppingTests

namespace OAI

/-! The actual common convex tails preserve the conditional decomposition
at every Brownian stopping time, including infinite stops. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

def convexStoppingCurrentMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℕ → ℝ) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (n : ℕ) (S : Ω → ℝ≥0∞) :
    Measure upperHalfPlane :=
  ∑ i ∈ s n, ENNReal.ofReal (w n i) • P.bind (halfPlaneStoppingCurrentMeasure κ B γ G (u (n+i)) S)

lemma convexLevelMeasure_random_time_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (n : ℕ) (S : Ω → ℝ≥0∞) (hS : Measurable S) :
    Measurable (fun ω => convexLevelMeasure κ B γ G u s w n (S ω) ω) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [convexLevelMeasure,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul ((Measure.measurable_coe hA).comp
    (halfPlaneLevelMeasure_random_time_measurable hm hc κ (u (n+i)) (hu _) γ G F hw S hS))

lemma convexLevelMeasure_stopping_conditional_split
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (n : ℕ) (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) S)
    (E : Set Ω) (hE : MeasurableSet[hS.measurableSpace] E) :
    (P.restrict E).bind (convexLevelMeasure κ B γ G u s w n ∞) =
      (P.restrict E).bind (fun ω => convexLevelMeasure κ B γ G u s w n (S ω) ω) +
        convexStoppingCurrentMean (P.restrict E) κ B γ G u s w n S := by
  let hm (r : ℝ≥0) : Measurable (B r) := hBm.comp (measurable_const.prodMk measurable_id)
  unfold convexLevelMeasure convexStoppingCurrentMean
  rw [bind_finset_smul _ _ _ (fun _ => ENNReal.ofReal_ne_top) _
      (fun i => halfPlaneLevelMeasure_measurable hm hc κ (u (n+i)) (hu _) γ G F hw ∞),
    bind_finset_smul _ _ _ (fun _ => ENNReal.ofReal_ne_top) _
      (fun i => halfPlaneLevelMeasure_random_time_measurable hm hc κ (u (n+i)) (hu _)
        γ G F hw S hS.measurable')]
  simp_rw [halfPlaneLevelMeasure_stopping_conditional_split hB hBm hc hB0 hκ hκ8 γ G F hw
    _ (hu _) S hS E hE,smul_add,Finset.sum_add_distrib]

lemma convexStoppingCurrentMean_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (n : ℕ) (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) S)
    (E : Set Ω) :
    convexStoppingCurrentMean (P.restrict E) κ B γ G u s w n S ≤ initialGreenMeasure κ := by
  apply Measure.le_iff.mpr
  intro A _
  simp only [convexStoppingCurrentMean,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∑ i ∈ s n, ENNReal.ofReal (w n i) * initialGreenMeasure κ A :=
      Finset.sum_le_sum (fun i _ => mul_le_mul' le_rfl
        (halfPlaneStoppingCurrentMeasure_mean_le hB hBm hc hB0 hκ hκ8 γ G F hw
          (u (n+i)) (hu _) S hS E A))
    _ = _ := by
      rw [← Finset.sum_mul,← ENNReal.ofReal_sum_of_nonneg (hw₀ n),hw₁ n,ENNReal.ofReal_one,one_mul]

theorem convexStoppingCurrentMean_test_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u) (hlim : Tendsto u atTop atTop)
    (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) S)
    (E : Set Ω) (f : C_c(upperHalfPlane,ℝ)) :
    Tendsto (fun n => ∫ z, f z ∂convexStoppingCurrentMean (P.restrict E) κ B γ G u s w n S)
      atTop (𝓝 (∫ z, f z ∂(P.restrict E).bind (halfPlaneStoppingGreenMeasure κ B γ G S))) := by
  let ρ := initialGreenMeasure κ
  let : IsFiniteMeasureOnCompacts ρ := initialGreenMeasure_finite_on_compacts κ
  let μ (j : ℕ) := (P.restrict E).bind (halfPlaneStoppingCurrentMeasure κ B γ G (u j) S)
  have hμ (j : ℕ) : μ j ≤ ρ :=
    halfPlaneStoppingCurrentMeasure_mean_le hB hBm hc hB0 hκ hκ8 γ G F hw (u j) (hu j) S hS E
  have hfi (j : ℕ) : Integrable f (μ j) := f.integrable.mono_measure (hμ j)
  have he (n : ℕ) : (∫ z, f z ∂convexStoppingCurrentMean (P.restrict E) κ B γ G u s w n S) =
      ∑ i ∈ s n, w n i * (∫ z, f z ∂μ (n+i)) := by
    have hi (i : ℕ) : Integrable f (ENNReal.ofReal (w n i) • μ (n+i)) :=
      (hfi (n+i)).smul_measure ENNReal.ofReal_ne_top
    change (∫ z, f z ∂∑ i ∈ s n, ENNReal.ofReal (w n i) • μ (n+i)) = _
    rw [integral_finsetSum_measure (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i his
    rw [integral_smul_measure,ENNReal.toReal_ofReal (hw₀ n i his),smul_eq_mul]
  simp only [he]
  exact real_convex_tail_tendsto (fun j => ∫ z, f z ∂μ j)
    (halfPlaneStoppingCurrentMeasure_mean_test_tendsto hB hBm hc hB0 hκ hκ8 γ G F hw
      u hu hmono hlim S hS E f) s w hw₀ hw₁

end SLEExactGauge.Multipoint

end

end OAI
