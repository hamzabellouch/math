import OAI.Probability.SLE.Mass.CompactLevelMoments

namespace OAI

/-! Bounded nonnegative tests of the actual finite-level measures inherit
the compact moment bounds used for simultaneous convex extraction. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

def levelApproximationTest {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (t : ℝ≥0∞) (f : ℂ → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ z, f z ∂levelApproximation κ B γ G u t ω

lemma lintegral_le_const_mul_measure_of_support
    (μ : Measure ℂ) (K : Set ℂ) (hK : MeasurableSet K)
    (f : ℂ → ℝ≥0∞) (C : ℝ≥0∞) (hf : ∀ z ∈ K, f z ≤ C)
    (hz : ∀ z ∉ K, f z = 0) : (∫⁻ z, f z ∂μ) ≤ C * μ K := by
  classical
  apply (lintegral_mono (fun z => ?_)).trans (lintegral_indicator_const hK C).le
  by_cases h : z ∈ K
  · simpa only [indicator_of_mem h] using hf z h
  · simp only [hz z h,indicator_of_notMem h,le_refl]

lemma levelApproximationTest_le
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (t : ℝ≥0∞) (f : ℂ → ℝ≥0∞) (ω : Ω)
    (K : Set ℂ) (hK : MeasurableSet K) (C : ℝ≥0∞)
    (hf : ∀ z ∈ K, f z ≤ C) (hz : ∀ z ∉ K, f z = 0) :
    levelApproximationTest κ B γ G u t f ω ≤ C * levelMass κ B γ G u K ω := by
  apply (lintegral_le_const_mul_measure_of_support
    (levelApproximation κ B γ G u t ω) K hK f C hf hz).trans
  gcongr
  exact levelApproximation_apply_le κ B γ G u t ω hK

lemma levelApproximationTest_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0∞) (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    Measurable (levelApproximationTest κ B γ G u t f) := by
  have hd := levelApproximationDensity_joint_measurable hm hBc κ u hu γ G F hw t
  have he (ω : Ω) : levelApproximationTest κ B γ G u t f ω =
      ∫⁻ z, levelApproximationDensity κ B γ G u t ω z * f z := by
    exact lintegral_withDensity_eq_lintegral_mul volume hd.of_uncurry_left hf
  simp_rw [show levelApproximationTest κ B γ G u t f =
    (fun ω => ∫⁻ z, levelApproximationDensity κ B γ G u t ω z * f z) from funext he]
  exact (hd.mul (hf.comp measurable_snd)).lintegral_prod_right'

theorem uniform_levelApproximationTest_moments
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane)
    (f : ℂ → ℝ≥0∞) (C : ℝ≥0∞) (hC : C < ⊤)
    (hf : ∀ z ∈ K, f z ≤ C) (hz : ∀ z ∉ K, f z = 0) (m : ℕ) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ u : ℝ, 0 ≤ u → ∀ t : ℝ≥0∞,
      (∫⁻ ω, levelApproximationTest κ B γ G u t f ω ^ m ∂P) ≤ M := by
  obtain ⟨M,hM,hbound⟩ := uniform_levelMass_compact_moments hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth K hK hKH m
  refine ⟨C^m*M,ENNReal.mul_lt_top (ENNReal.pow_lt_top hC) hM,?_⟩
  intro u hu t
  calc
    _ ≤ ∫⁻ ω, (C*levelMass κ B γ G u K ω)^m ∂P :=
      lintegral_mono (fun ω => pow_le_pow_left'
        (levelApproximationTest_le κ B γ G u t f ω K hK.measurableSet C hf hz) m)
    _ = C^m*(∫⁻ ω, levelMass κ B γ G u K ω ^ m ∂P) := by
      simp_rw [mul_pow]
      exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top hC.ne)
    _ ≤ _ := by gcongr; exact hbound u hu

end SLEExactGauge.Multipoint

end

end OAI
