import OAI.Probability.SLE.Mass.LevelCurrentTests
import OAI.Probability.SLE.Mass.ConvexMeanMeasure
import OAI.Probability.SLE.Mass.LevelRandomRadon

namespace OAI

/-! The exact conditional decomposition is preserved by the common
finite convex combinations. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge

lemma bind_mono_of_measurable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) {μ ν : Ω → Measure X} (hμ : Measurable μ) (hν : Measurable ν)
    (h : ∀ ω, μ ω ≤ ν ω) : P.bind μ ≤ P.bind ν := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA hμ.aemeasurable,Measure.bind_apply hA hν.aemeasurable]
  exact lintegral_mono (fun ω => h ω A)

lemma bind_finset_smul {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (s : Finset ℕ) (w : ℕ → ℝ≥0∞) (hw : ∀ i, w i ≠ ⊤)
    (μ : ℕ → Ω → Measure X) (hμ : ∀ i, Measurable (μ i)) :
    P.bind (fun ω => ∑ i ∈ s, w i • μ i ω) = ∑ i ∈ s, w i • P.bind (μ i) := by
  have hm : Measurable (fun ω => ∑ i ∈ s, w i • μ i ω) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.mul ((Measure.measurable_coe hA).comp (hμ i)))
  apply Measure.ext
  intro A hA
  rw [Measure.bind_apply hA hm.aemeasurable]
  simp only [Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  rw [lintegral_finsetSum s (f := fun i ω => w i * μ i ω A)
    (fun i _ => measurable_const.mul ((Measure.measurable_coe hA).comp (hμ i)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_const_mul' _ _ (hw i),Measure.bind_apply hA (hμ i).aemeasurable]

namespace Multipoint

lemma halfPlaneLevelMeasure_conditional_split
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0) (E : Set Ω)
    (hE : MeasurableSet[Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable) t] E) :
    (P.restrict E).bind (halfPlaneLevelMeasure κ B γ G u ∞) =
      (P.restrict E).bind (halfPlaneLevelMeasure κ B γ G u t) +
      (P.restrict E).bind (halfPlaneCurrentMeasure κ B γ G u t) := by
  let hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  rw [← halfPlaneRemainderMeasure_conditional_mean hB hBm hBc hB0 hκ hκ8 γ G F hw u hu t E hE]
  apply Measure.ext
  intro A hA
  rw [Measure.add_apply,
    Measure.bind_apply hA (halfPlaneLevelMeasure_measurable hm hBc κ u hu γ G F hw ∞).aemeasurable,
    Measure.bind_apply hA (halfPlaneLevelMeasure_measurable hm hBc κ u hu γ G F hw t).aemeasurable,
    Measure.bind_apply hA (halfPlaneRemainderMeasure_measurable hm hBc κ u hu γ G F hw t).aemeasurable]
  simp_rw [halfPlaneLevelMeasure_split hm hBc κ u hu γ G F hw t,Measure.add_apply]
  exact lintegral_add_left (((Measure.measurable_coe hA).comp
    (halfPlaneLevelMeasure_measurable hm hBc κ u hu γ G F hw t))) _

def convexCurrentMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℕ → ℝ) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (n : ℕ) (t : ℝ≥0) :
    Measure upperHalfPlane :=
  ∑ i ∈ s n, ENNReal.ofReal (w n i) • P.bind (halfPlaneCurrentMeasure κ B γ G (u (n+i)) t)

lemma convexLevelMeasure_conditional_split
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (n : ℕ) (t : ℝ≥0) (E : Set Ω)
    (hE : MeasurableSet[Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable) t] E) :
    (P.restrict E).bind (convexLevelMeasure κ B γ G u s w n ∞) =
      (P.restrict E).bind (convexLevelMeasure κ B γ G u s w n t) +
        convexCurrentMean (P.restrict E) κ B γ G u s w n t := by
  let hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  unfold convexLevelMeasure convexCurrentMean
  rw [bind_finset_smul _ _ _ (fun _ => ENNReal.ofReal_ne_top) _
      (fun i => halfPlaneLevelMeasure_measurable hm hBc κ (u (n+i)) (hu _) γ G F hw ∞),
    bind_finset_smul _ _ _ (fun _ => ENNReal.ofReal_ne_top) _
      (fun i => halfPlaneLevelMeasure_measurable hm hBc κ (u (n+i)) (hu _) γ G F hw t)]
  simp_rw [halfPlaneLevelMeasure_conditional_split hB hBm hBc hB0 hκ hκ8 γ G F hw
    _ (hu _) t E hE,smul_add,Finset.sum_add_distrib]


lemma convexLevelMeasure_mean_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (n : ℕ) (t : ℝ≥0∞) (E : Set Ω) :
    (P.restrict E).bind (convexLevelMeasure κ B γ G u s w n t) ≤ initialGreenMeasure κ := by
  let hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  rw [← convexLevelMeasure_terminal_mean hB hm hBm hBc hB0 hκ hκ8 γ G F hw u hu s w hw₀ hw₁ n]
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA (convexLevelMeasure_measurable hm hBc κ γ G F hw u hu s w n t).aemeasurable,
    Measure.bind_apply hA (convexLevelMeasure_measurable hm hBc κ γ G F hw u hu s w n ∞).aemeasurable]
  exact lintegral_mono' Measure.restrict_le_self (fun ω =>
    convexLevelMeasure_mono κ B γ G u s w n ω le_top A)

lemma convexCurrentMean_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (n : ℕ) (t : ℝ≥0) (E : Set Ω) :
    convexCurrentMean (P.restrict E) κ B γ G u s w n t ≤ initialGreenMeasure κ := by
  apply Measure.le_iff.mpr
  intro A _
  simp only [convexCurrentMean,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∑ i ∈ s n, ENNReal.ofReal (w n i) * initialGreenMeasure κ A :=
      Finset.sum_le_sum (fun i _ => mul_le_mul' le_rfl
        (halfPlaneCurrentMeasure_mean_le hB hBm hBc hB0 hκ hκ8 γ G F hw (u (n+i)) (hu _) t E A))
    _ = _ := by
      rw [← Finset.sum_mul,← ENNReal.ofReal_sum_of_nonneg (hw₀ n),hw₁ n,ENNReal.ofReal_one,one_mul]

end Multipoint
end SLEExactGauge

end

end OAI
