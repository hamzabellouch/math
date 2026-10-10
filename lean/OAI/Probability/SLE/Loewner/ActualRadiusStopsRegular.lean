import OAI.Probability.SLE.Loewner.ActualRadiusStops

namespace OAI

/-! For a regular Brownian driver with an actual capacity witness at every
sample, the literal geometric radius-level time is a stopping time. No
modification on an exceptional set is needed. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem actual_radiusLevelTime_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) :
    IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (radiusLevelTime (γ ω) (G ω) z u : WithTop ℝ≥0)) := by
  let A₀ := logAngleSq κ (initialLogCoordinates z) 0
  have hA₀ : 0 < A₀ := logAngleSq_pos _ _ _
  let ε (n : ℕ) := A₀ / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε₀ (n : ℕ) : ε n ≤ A₀ :=
    div_le_self hA₀.le (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A₀
    simpa only [mul_one_div, mul_zero] using hh
  let a (n : ℕ) : AngularLocalization B hm κ z u (ε n) :=
    Classical.choice (exists_angularLocalization hB hm hBm hc hB0 κ hκ hκ8 z u
      (ε n) hu (hε n) (hε₀ n))
  have he : localizedRadiusStop a = fun ω => radiusLevelTime (γ ω) (G ω) z u := by
    funext ω
    exact localizedRadiusStop_eq_source a hεlim hc hz ω (γ ω) (G ω) (F ω) (hw ω)
  rw [← he]
  exact localizedRadiusStop_stopping a

lemma actual_radiusLevelTime_past_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
    (actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz u hu).measurableSpace ≤
      (actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz v
        (hu.trans huv)).measurableSpace :=
  (actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz u hu).measurableSpace_mono
    (actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz v (hu.trans huv))
    (fun ω => radiusLevelTime_mono ((hc ω).const_mul _) (hw ω) z hu huv)

end SLEExactGauge

end

end OAI
