import OAI.Probability.SLE.Mass.LevelGreenLimit
import OAI.Probability.SLE.FiniteMass

namespace OAI

/-! Finite centered clock tightness implies decay of the ordinary killed
Green potential. No infinite centered probability space is needed. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

lemma ofReal_mul_integral_div {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (hY : Integrable Y P)
    (hYn : ∀ᵐ ω ∂P, 0 ≤ Y ω) (g : ℝ) (hg : 0 < g) :
    ENNReal.ofReal g * ENNReal.ofReal ((∫ ω, Y ω ∂P) / g) =
      ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P := by
  rw [← ENNReal.ofReal_mul hg.le,← ofReal_integral_eq_lintegral_ofReal hY hYn]
  congr 1
  field_simp

lemma actual_radius_tail_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun s => B s ω))
    (κ u : ℝ) (hu : 0 ≤ u) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (t : ℝ≥0) :
    MeasurableSet {ω | (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u} := by
  have hτ := actual_radiusLevel_joint_measurable hm hBc κ u hu γ G F hw
  have hlt := measurableSet_lt (measurable_const (a := (t : ℝ≥0∞))) hτ
  have hpre := hlt.preimage (measurable_id.prodMk (measurable_const (a := z)))
  exact hpre


lemma levelCurrentGreen_mean_eq_centered_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun s => B s ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal (levelCurrentGreen κ B γ G u t z ω) ∂P) =
      ENNReal.ofReal (initialGreen κ z) * finiteCenteredLaw P κ B γ G z u
        {ω | (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u} := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let A := {ω | (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z u}
  have hA : MeasurableSet A := actual_radius_tail_measurable
    (fun r => hBm.comp (measurable_const.prodMk measurable_id)) hBc κ u hu γ G F hw z t
  have hi := (finite_stopped_green_regular hB hBm hBc hB0 κ hκ hκ8 γ G F
    (Eventually.of_forall hw) z hz u hu).1
  have he := levelRemainderGreen_setLIntegral hB hBm hBc hB0 hκ hκ8 γ G F
    (Eventually.of_forall hw) z hz u hu t univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at he
  rw [← he]
  change (∫⁻ ω, ENNReal.ofReal (if ω ∈ A then
    stoppedGreen κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) z u else 0) ∂P) = _
  trans (∫⁻ ω in A, ENNReal.ofReal
    (stoppedGreen κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) z u) ∂P)
  · rw [← lintegral_indicator hA]
    apply lintegral_congr
    intro ω
    by_cases hω : ω ∈ A
    · rw [ite_eq_left hω,indicator_of_mem hω]
    · rw [ite_eq_right hω,indicator_of_notMem hω,ENNReal.ofReal_zero]
  · rw [finiteCenteredLaw_apply hB κ hκ hκ8 γ G F (Eventually.of_forall hw) z hz u hu A hA]
    exact (ofReal_mul_integral_div (P.restrict A) _ hi.integrableOn
      (Eventually.of_forall (fun ω => stoppedGreen_nonneg (hw ω) κ z u)) _
        (initialGreen_pos κ z hz)).symm


lemma greenDensity_mean_le_of_level_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun s => B s ω)) {κ : ℝ}
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (t : ℝ≥0) (C : ℝ≥0∞)
    (hbound : ∀ n : ℕ, (∫⁻ ω, ENNReal.ofReal
      (levelCurrentGreen κ B γ G n t z ω) ∂P) ≤ C) :
    (∫⁻ ω, ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ * B s ω)
      (γ ω) (G ω) t z) ∂P) ≤ C := by
  have hm (n : ℕ) : Measurable (fun ω => ENNReal.ofReal (levelCurrentGreen κ B γ G n t z ω)) :=
    ((levelCurrentGreen_joint_measurable hBm hBc κ n (Nat.cast_nonneg n) γ G F hw t).comp
      (measurable_id.prodMk measurable_const)).ennreal_ofReal
  have hmono : ∀ᵐ ω ∂P, Monotone (fun n : ℕ => ENNReal.ofReal (levelCurrentGreen κ B γ G n t z ω)) := by
    filter_upwards [] with ω
    intro m n hmn
    exact ENNReal.ofReal_le_ofReal (levelCurrentGreen_mono ω (hBc ω) (hw ω) z t
      (Nat.cast_nonneg m) (Nat.cast_le.mpr hmn))
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ENNReal.ofReal (levelCurrentGreen κ B γ G n t z ω))
      atTop (𝓝 (ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ * B s ω)
        (γ ω) (G ω) t z))) := by
    filter_upwards [] with ω
    apply tendsto_const_nhds.congr'
    exact (levelCurrentGreen_eventually_eq ω (hBc ω) (hw ω) z t (fun n : ℕ => (n:ℝ))
      (fun n => Nat.cast_nonneg n) tendsto_natCast_atTop_atTop).mono
      (fun _ h => congrArg ENNReal.ofReal h.symm)
  exact le_of_tendsto (lintegral_tendsto_of_tendsto_of_monotone (fun n => (hm n).aemeasurable)
    hmono hlim) (Eventually.of_forall hbound)

theorem greenDensity_mean_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun s => B s ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) :
    Tendsto (fun t : ℝ≥0 => ∫⁻ ω, ENNReal.ofReal
      (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z) ∂P)
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  apply ENNReal.tendsto_atTop_zero.mpr
  intro ε hε
  by_cases he : ε = ∞
  · exact ⟨0,fun _ _ => he ▸ le_top⟩
  let δ := ε.toReal / initialGreen κ z
  have hδ : 0 < δ := div_pos (ENNReal.toReal_pos hε.ne' he) (initialGreen_pos κ z hz)
  obtain ⟨T,_,hT⟩ := finite_physical_clock_tight hB κ hκ hκ8 γ G F
    (Eventually.of_forall hw) z hz δ hδ
  refine ⟨T,fun t ht => ?_⟩
  apply greenDensity_mean_le_of_level_bound hBm hBc γ G F hw z t ε
  intro n
  rw [levelCurrentGreen_mean_eq_centered_tail hB hBm hBc hB0 hκ hκ8 γ G F hw z hz
    n (Nat.cast_nonneg n) t]
  have htail : finiteCenteredLaw P κ B γ G z n
      {ω | (t:ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z n} ≤ ENNReal.ofReal δ :=
    (measure_mono (fun ω hω => (ENNReal.coe_le_coe.mpr ht).trans_lt hω)).trans (hT n)
  apply (mul_le_mul' le_rfl htail).trans_eq
  rw [← ENNReal.ofReal_mul (initialGreen_pos κ z hz).le]
  have hc : initialGreen κ z * δ = ε.toReal := by
    dsimp only [δ]
    exact mul_div_cancel₀ _ (initialGreen_pos κ z hz).ne'
  rw [hc,ENNReal.ofReal_toReal he]

end SLEExactGauge.Multipoint

end

end OAI
