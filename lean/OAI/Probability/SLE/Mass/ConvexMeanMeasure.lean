import OAI.Probability.SLE.Mass.LevelMeanMeasure
import OAI.Probability.SLE.Mass.LevelRadonExtraction

namespace OAI

/-! The common convex coefficients preserve the exact terminal mean
measure, including signed compact tests. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

lemma convexLevelMeasure_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (n : ℕ) (t : ℝ≥0∞) : Measurable (convexLevelMeasure κ B γ G u s w n t) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [convexLevelMeasure,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.mul ((Measure.measurable_coe hA).comp
    (halfPlaneLevelMeasure_measurable hm hBc κ (u (n+i)) (hu _) γ G F hw t))

theorem convexLevelMeasure_terminal_mean
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (n : ℕ) : P.bind (convexLevelMeasure κ B γ G u s w n ∞) = initialGreenMeasure κ := by
  apply Measure.ext
  intro A hA
  rw [Measure.bind_apply hA (convexLevelMeasure_measurable hm hBc κ γ G F hw u hu s w n ∞).aemeasurable]
  simp only [convexLevelMeasure,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  rw [lintegral_finsetSum (s n) (f := fun i ω => ENNReal.ofReal (w n i) *
    halfPlaneLevelMeasure κ B γ G (u (n+i)) ∞ ω A)
    (fun i _ => measurable_const.mul ((Measure.measurable_coe hA).comp
      (halfPlaneLevelMeasure_measurable hm hBc κ (u (n+i)) (hu _) γ G F hw ∞)))]
  have he (i : ℕ) : (∫⁻ ω, halfPlaneLevelMeasure κ B γ G (u (n+i)) ∞ ω A ∂P) =
      initialGreenMeasure κ A := by
    rw [← Measure.bind_apply hA (halfPlaneLevelMeasure_measurable hm hBc κ (u (n+i)) (hu _) γ G F hw ∞).aemeasurable,
      halfPlaneLevelMeasure_terminal_mean hB hm hBm hBc hB0 hκ hκ8 γ G F hw (u (n+i)) (hu _)]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,he]
  rw [← Finset.sum_mul,← ENNReal.ofReal_sum_of_nonneg (hw₀ n),hw₁ n,ENNReal.ofReal_one,one_mul]

theorem convexLevelMeasure_terminal_test_mean
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (n : ℕ) (f : C_c(upperHalfPlane,ℝ)) :
    Integrable (fun ω => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n ∞ ω) P ∧
      (∫ ω, (∫ z, f z ∂convexLevelMeasure κ B γ G u s w n ∞ ω) ∂P) =
        ∫ z, f z ∂initialGreenMeasure κ := by
  have he := convexLevelMeasure_terminal_mean hB hm hBm hBc hB0 hκ hκ8 γ G F hw
    u hu s w hw₀ hw₁ n
  have hi (ω : Ω) : Integrable f (convexLevelMeasure κ B γ G u s w n ∞ ω) := by
    let := convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω) u s w n ∞
    exact f.integrable
  have hiP : Integrable f (P.bind (convexLevelMeasure κ B γ G u s w n ∞)) := by
    rw [he]
    let := initialGreenMeasure_finite_on_compacts κ
    exact f.integrable
  simpa only [he] using integrable_integral_bind_of_sections P _
    (convexLevelMeasure_measurable hm hBc κ γ G F hw u hu s w n ∞) f f.continuous.measurable hi hiP

end SLEExactGauge.Multipoint

end

end OAI
