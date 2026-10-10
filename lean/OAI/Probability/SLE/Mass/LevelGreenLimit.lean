import OAI.Probability.SLE.Mass.LevelApproximationKernel
import OAI.Probability.SLE.Multipoint.MultipointRadiusStatus

namespace OAI

/-! As the radius level tends to infinity, the remaining finite-level
kernel increases to the killed Green potential. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

lemma levelCurrentGreen_mono
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hBc : Continuous (fun s => B s ω))
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (t : ℝ≥0) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    levelCurrentGreen κ B γ G u t z ω ≤ levelCurrentGreen κ B γ G v t z ω := by
  have hτ := radiusLevelTime_mono (hBc.const_mul _) hw z hu huv
  unfold levelCurrentGreen
  split_ifs with h₁ h₂
  · exact le_rfl
  · exact False.elim (h₂ (h₁.trans_le hτ))
  · exact greenDensity_nonneg hw κ t z
  · exact le_rfl

lemma levelCurrentGreen_eventually_eq
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hBc : Continuous (fun s => B s ω))
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (t : ℝ≥0) (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hlim : Tendsto u atTop atTop) :
    ∀ᶠ n in atTop, levelCurrentGreen κ B γ G (u n) t z ω =
      greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z := by
  by_cases hz : z ∈ survivingDomain (γ ω) t
  · filter_upwards [hlim.eventually (eventually_gt_atTop
      (logRadiusClock (Real.log z.im) (logLoewnerCoordinates (G ω) z t)))] with n hn
    have hτ : (t : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z (u n) := by
      apply lt_of_not_ge
      rw [radiusLevelTime_le_iff_clock (hBc.const_mul _) hw z (u n) (hu n) t hz]
      exact not_le.mpr hn
    exact ite_eq_left hτ
  · filter_upwards [] with n
    unfold levelCurrentGreen greenDensity
    simp only [ite_eq_right hz,ite_self]

theorem levelCurrentGreen_mean_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun s => B s ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal (levelCurrentGreen κ B γ G u t z ω) ∂P) ≤
      ENNReal.ofReal (initialGreen κ z) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have he := levelRemainderGreen_setLIntegral hB hBm hBc hB0 hκ hκ8 γ G F
    (ae_of_all _ hw) z hz u hu t univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at he
  rw [← he]
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (stoppedGreen κ (fun s => Real.sqrt κ * B s ω)
        (γ ω) (G ω) z u) ∂P := by
      apply lintegral_mono
      intro ω
      unfold levelRemainderGreen
      dsimp only
      split_ifs
      · exact le_rfl
      · rw [ENNReal.ofReal_zero]
        positivity
    _ = _ := by
      obtain ⟨hi,he⟩ := finite_stopped_green_regular hB hBm hBc hB0 κ hκ hκ8 γ G F
        (ae_of_all _ hw) z hz u hu
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ (fun ω => stoppedGreen_nonneg (hw ω) κ z u)),he]

theorem greenDensity_mean_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun s => B s ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (t : ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ * B s ω)
      (γ ω) (G ω) t z) ∂P) ≤ ENNReal.ofReal (initialGreen κ z) := by
  have hm (n : ℕ) : Measurable (fun ω => ENNReal.ofReal (levelCurrentGreen κ B γ G n t z ω)) := by
    have hj := (levelCurrentGreen_joint_measurable hBm hBc κ n (Nat.cast_nonneg n) γ G F hw t).ennreal_ofReal
    have hp : Measurable (fun ω : Ω => (ω,z)) := measurable_id.prodMk measurable_const
    have hh := hj.comp hp
    simpa only [Function.comp_def] using hh
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
    exact (levelCurrentGreen_eventually_eq ω (hBc ω) (hw ω) z t (fun n : ℕ => (n : ℝ))
      (fun n => Nat.cast_nonneg n) tendsto_natCast_atTop_atTop).mono (fun _ h => congrArg ENNReal.ofReal h.symm)
  exact le_of_tendsto (lintegral_tendsto_of_tendsto_of_monotone (fun n => (hm n).aemeasurable) hmono hlim)
    (Eventually.of_forall (fun n => levelCurrentGreen_mean_le hB hBm hBc hB0 hκ hκ8 γ G F hw z hz
      n (Nat.cast_nonneg n) t))

end SLEExactGauge.Multipoint

end

end OAI
