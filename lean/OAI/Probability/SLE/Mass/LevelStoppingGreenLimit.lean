import OAI.Probability.SLE.Mass.LevelStoppingSpatialKernel
import OAI.Probability.SLE.Mass.LevelGreenLimit

namespace OAI

/-! Increasing finite radius levels recover the Green kernel killed at an
arbitrary stopping time. Its expectation is bounded by the initial Green
function, also when the stopping time may be infinite. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

def stoppingGreen {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (S : Ω → ℝ≥0∞) (z : ℂ) (ω : Ω) : ℝ :=
  if S ω < ∞ then greenDensity κ (fun s => Real.sqrt κ * B s ω)
    (γ ω) (G ω) (S ω).toNNReal z else 0

lemma levelStoppingCurrentGreen_mono
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hc : Continuous (fun s => B s ω))
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (S : Ω → ℝ≥0∞) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    levelStoppingCurrentGreen κ B γ G u S z ω ≤ levelStoppingCurrentGreen κ B γ G v S z ω := by
  have hτ := radiusLevelTime_mono (hc.const_mul _) hw z hu huv
  unfold levelStoppingCurrentGreen
  split_ifs with h₁ h₂
  · exact le_rfl
  · exact False.elim (h₂ (h₁.trans_le hτ))
  · exact greenDensity_nonneg hw κ _ z
  · exact le_rfl

lemma levelStoppingCurrentGreen_eventually_eq
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hc : Continuous (fun s => B s ω))
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (S : Ω → ℝ≥0∞) (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hlim : Tendsto u atTop atTop) :
    ∀ᶠ n in atTop, levelStoppingCurrentGreen κ B γ G (u n) S z ω = stoppingGreen κ B γ G S z ω := by
  by_cases hfin : S ω < ∞
  · have hcoe : ((S ω).toNNReal : ℝ≥0∞) = S ω := ENNReal.coe_toNNReal hfin.ne
    filter_upwards [levelCurrentGreen_eventually_eq ω hc hw z (S ω).toNNReal u hu hlim] with n hn
    simpa only [levelCurrentGreen,levelStoppingCurrentGreen,stoppingGreen,hcoe,ite_eq_left hfin] using hn
  · have htop : S ω = ∞ := top_le_iff.mp (le_of_not_gt hfin)
    filter_upwards [] with n
    simp [levelStoppingCurrentGreen,stoppingGreen,htop]

theorem levelStoppingCurrentGreen_mean_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u)
    (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) S) :
    (∫⁻ ω, ENNReal.ofReal (levelStoppingCurrentGreen κ B γ G u S z ω) ∂P) ≤
      ENNReal.ofReal (initialGreen κ z) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have he := levelStoppingRemainderGreen_setLIntegral hB hBm hc hB0 hκ hκ8
    γ G F hw z hz u hu S hS univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at he
  rw [← he]
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (stoppedGreen κ (fun s => Real.sqrt κ * B s ω)
        (γ ω) (G ω) z u) ∂P := by
      apply lintegral_mono
      intro ω
      unfold levelStoppingRemainderGreen
      dsimp only
      split_ifs
      · exact le_rfl
      · simp only [ENNReal.ofReal_zero]
        exact bot_le
    _ = _ := by
      obtain ⟨hi,he⟩ := finite_stopped_green_regular hB hBm hc hB0 κ hκ hκ8 γ G F
        (ae_of_all _ hw) z hz u hu
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ (fun ω => stoppedGreen_nonneg (hw ω) κ z u)),he]

theorem stoppingGreen_mean_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (S : Ω → WithTop ℝ≥0)
    (hS : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) S) :
    (∫⁻ ω, ENNReal.ofReal (stoppingGreen κ B γ G S z ω) ∂P) ≤
      ENNReal.ofReal (initialGreen κ z) := by
  have hm (n : ℕ) : Measurable (fun ω => ENNReal.ofReal
      (levelStoppingCurrentGreen κ B γ G n S z ω)) := by
    have hj := (levelStoppingCurrentGreen_joint_measurable hBm hc κ n (Nat.cast_nonneg n)
      γ G F hw S hS.measurable').ennreal_ofReal
    have hh := hj.comp (measurable_id.prodMk (measurable_const (a := z)))
    simpa only [Function.comp_def,id_eq] using hh
  have hmono : ∀ᵐ ω ∂P, Monotone (fun n : ℕ => ENNReal.ofReal
      (levelStoppingCurrentGreen κ B γ G n S z ω)) := by
    filter_upwards [] with ω
    intro n k hnk
    exact ENNReal.ofReal_le_ofReal (levelStoppingCurrentGreen_mono ω (hc ω) (hw ω)
      z S (Nat.cast_nonneg n) (Nat.cast_le.mpr hnk))
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ENNReal.ofReal
      (levelStoppingCurrentGreen κ B γ G n S z ω)) atTop
      (𝓝 (ENNReal.ofReal (stoppingGreen κ B γ G S z ω))) := by
    filter_upwards [] with ω
    apply tendsto_const_nhds.congr'
    exact (levelStoppingCurrentGreen_eventually_eq ω (hc ω) (hw ω) z S
      (fun n : ℕ => (n:ℝ)) (fun n => Nat.cast_nonneg n) tendsto_natCast_atTop_atTop).mono
      (fun _ he => congrArg ENNReal.ofReal he.symm)
  exact le_of_tendsto (lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hm n).aemeasurable) hmono hlim)
    (Eventually.of_forall (fun n => levelStoppingCurrentGreen_mean_le hB hBm hc hB0 hκ hκ8
      γ G F hw z hz n (Nat.cast_nonneg n) S hS))

end SLEExactGauge.Multipoint

end

end OAI
