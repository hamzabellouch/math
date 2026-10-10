import OAI.Probability.SLE.Mass.LevelRadonExtraction
import OAI.Probability.SLE.Mass.RandomRadonLimit
import OAI.Probability.SLE.Mass.RadonTestLimitProperties

namespace OAI

/-! Measurable versions and simultaneous time ordering of the actual
common Radon limits. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma halfPlaneLevelMeasure_mono
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) (u : ℝ) (ω : Ω) :
    Monotone (fun t => halfPlaneLevelMeasure κ B γ G u t ω) := by
  intro s t hst
  apply Measure.le_iff.mpr
  intro A hA
  simp only [halfPlaneLevelMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet]
  exact levelApproximation_mono κ B γ G u ω hst _

lemma convexLevelMeasure_mono
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) (u : ℕ → ℝ)
    (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (n : ℕ) (ω : Ω) :
    Monotone (fun t => convexLevelMeasure κ B γ G u s w n t ω) := by
  intro t₁ t₂ ht
  apply Measure.le_iff.mpr
  intro A hA
  simp only [convexLevelMeasure,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul' le_rfl
    (halfPlaneLevelMeasure_mono κ B γ G (u (n+i)) ω ht A))

lemma convexLevelMeasure_test_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (n : ℕ) (t : ℝ≥0∞)
    (f : C_c(upperHalfPlane,ℝ)) :
    Measurable (fun ω => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n t ω) := by
  have he (ω : Ω) := integral_convexLevelMeasure hκ hκ8 γ G F ω (hBc ω) (hw ω)
    u s w n t (hw₀ n) f
  simp_rw [he]
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.mul (levelApproximationRealTest_measurable hm hBc κ (u (n+i))
    (hu (n+i)) γ G F hw t (extendHalfPlaneTest f)
    (extendHalfPlaneTest_measurable f f.continuous.measurable))

theorem exists_measurable_level_radon_limits
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (t : ℕ → ℝ≥0∞) :
    ∃ s : ℕ → Finset ℕ, ∃ w : ℕ → ℕ → ℝ, ∃ ν : ℕ → Ω → Measure upperHalfPlane,
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧ (∀ n, ∑ i ∈ s n, w n i = 1) ∧
      (∀ j, Measurable (ν j)) ∧
      (∀ j ω, (ν j ω).Regular ∧ IsFiniteMeasureOnCompacts (ν j ω)) ∧
      (∀ᵐ ω ∂P,
        (∀ j (f : C_c(upperHalfPlane,ℝ)),
          Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n (t j) ω)
            atTop (𝓝 (∫ z, f z ∂ν j ω))) ∧
        ∀ i j, t i ≤ t j → ν i ω ≤ ν j ω) := by
  obtain ⟨s,w,hw₀,hw₁,hex⟩ := exists_common_level_radon_limits hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth u hu t
  have hex' : ∀ᵐ ω ∂P, ∃ ν : ℕ → Measure upperHalfPlane, (∀ j, (ν j).Regular) ∧
      ∀ j (f : C_c(upperHalfPlane,ℝ)),
        Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n (t j) ω)
          atTop (𝓝 (∫ z, f z ∂ν j)) := by
    filter_upwards [hex] with ω hω
    obtain ⟨ν,hν,hlim⟩ := hω
    exact ⟨ν,fun j => (hν j).1,hlim⟩
  obtain ⟨ν,hνm,hνr,hlim⟩ := exists_measurable_countable_radon_limits P
    (fun n j ω => convexLevelMeasure κ B γ G u s w n (t j) ω)
    (fun n j f => convexLevelMeasure_test_measurable hm hBc hκ hκ8 γ G F hw u hu s w hw₀ n (t j) f) hex'
  refine ⟨s,w,ν,hw₀,hw₁,hνm,hνr,?_⟩
  filter_upwards [hlim] with ω hω
  refine ⟨hω,?_⟩
  intro i j hij
  let (k : ℕ) : IsFiniteMeasureOnCompacts (convexLevelMeasure κ B γ G u s w k (t i) ω) :=
    convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω) u s w k (t i)
  let (k : ℕ) : IsFiniteMeasureOnCompacts (convexLevelMeasure κ B γ G u s w k (t j) ω) :=
    convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω) u s w k (t j)
  let : (ν i ω).Regular := (hνr i ω).1
  let : (ν j ω).Regular := (hνr j ω).1
  exact radon_limits_mono _ _ (ν i ω) (ν j ω) (hω i) (hω j)
    (fun k => convexLevelMeasure_mono κ B γ G u s w k ω hij)

end SLEExactGauge.Multipoint

end

end OAI
