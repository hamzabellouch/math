import OAI.Probability.SLE.Mass.LevelApproximants

namespace OAI

/-! Mean measure of the actual finite-level approximants. This identity
uses the proved one-point stopped law and needs no univalence input. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

theorem levelMass_mean
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (K : Set ℂ) (hK : MeasurableSet K) (hKH : K ⊆ upperHalfPlane)
    (u : ℝ) (hu : 0 ≤ u) :
    (∫⁻ ω, levelMass κ B γ G u K ω ∂P) = ∫⁻ z in K, ENNReal.ofReal (initialGreen κ z) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  unfold levelMass
  rw [lintegral_lintegral_swap
    (actual_stoppedGreen_joint_measurable hm hBc κ u hu γ G F hw).ennreal_ofReal.aemeasurable]
  apply setLIntegral_congr_fun hK
  intro z hz
  obtain ⟨hi,he⟩ := finite_stopped_green_regular hB hBm hBc hB0 κ hκ hκ8 γ G F
    (ae_of_all _ hw) z (hKH hz) u hu
  dsimp only
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun ω =>
    stoppedGreen_nonneg (hw ω) κ z u)),he]

theorem levelApproximation_terminal_mean
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (K : Set ℂ) (hK : MeasurableSet K) (hKH : K ⊆ upperHalfPlane)
    (u : ℝ) (hu : 0 ≤ u) :
    (∫⁻ ω, levelApproximation κ B γ G u ∞ ω K ∂P) =
      ∫⁻ z in K, ENNReal.ofReal (initialGreen κ z) := by
  simp only [levelApproximation_apply_top κ B γ G u _ hK]
  exact levelMass_mean hB hm hBm hBc hB0 hκ hκ8 γ G F hw K hK hKH u hu

end SLEExactGauge.Multipoint

end

end OAI
