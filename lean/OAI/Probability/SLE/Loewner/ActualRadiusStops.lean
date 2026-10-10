import OAI.Probability.SLE.KernelExpectation
import OAI.Probability.SLE.Mass.DenseCoverMassTests

namespace OAI

/-! Geometric conformal-radius levels have increasing stopping-time
versions. Running maxima make the versions increasing on every outcome,
while preserving the actual geometric times almost surely. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma exists_live_level_of_radiusLevelTime_lt_top
    (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (u : ℝ)
    (h : radiusLevelTime γ G z u < ∞) :
    ∃ t : ℝ≥0, z ∈ survivingDomain γ t ∧
      fullRadius G t z = (2 * z.im) * Real.exp (-u) := by
  by_contra hn
  exact h.ne (radiusLevelTime_eq_top_of_no_level γ G z u hn)

lemma live_radius_level_before
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (z : ℂ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (T : ℝ≥0) (hT : z ∈ survivingDomain γ T)
    (hR : fullRadius G T z = (2 * z.im) * Real.exp (-v)) :
    ∃ t : ℝ≥0, t ≤ T ∧ z ∈ survivingDomain γ t ∧
      fullRadius G t z = (2 * z.im) * Real.exp (-u) := by
  let L : ℝ → ℝ := fun s => Real.log ((2 * z.im) / fullRadius G s.toNNReal z)
  have hy : 0 < 2 * z.im := mul_pos (by norm_num) hT.1.1
  have hz0 := survivingDomain_antitone γ (show (0 : ℝ≥0) ≤ T from zero_le) hT
  have hL0 : L 0 = 0 := by
    simp only [L, Real.toNNReal_zero, hw.fullRadius_initial hU z hz0,
      div_self hy.ne', Real.log_one]
  have hLT : L T = v := by
    dsimp only [L]
    rw [Real.toNNReal_coe, ← logRadiusClock_logCoordinates hU hw z T hT]
    exact (fullRadius_level_iff_logClock hU hw z T hT v).mp hR
  have hLc : ContinuousOn L (Icc 0 (T : ℝ)) :=
    fun s hs => (loewner_radius_clock_derivative hU hw T z hT s hs).continuousWithinAt
  obtain ⟨s, hs, hsu⟩ := intermediate_value_Icc T.coe_nonneg hLc
    (show u ∈ Icc (L 0) (L T) from ⟨by rwa [hL0], by rwa [hLT]⟩)
  have hsl := hw.live_at_real_time T z hT s hs.2
  refine ⟨s.toNNReal, Real.toNNReal_le_iff_le_coe.mpr hs.2, hsl, ?_⟩
  apply (fullRadius_level_iff_logClock hU hw z s.toNNReal hsl u).mpr
  rw [logRadiusClock_logCoordinates hU hw z s.toNNReal hsl]
  exact hsu

lemma radiusLevelTime_mono
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (z : ℂ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    radiusLevelTime γ G z u ≤ radiusLevelTime γ G z v := by
  by_cases hv : radiusLevelTime γ G z v = ∞
  · rw [hv]; exact le_top
  obtain ⟨T, hT, hR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G z v
    (lt_top_iff_ne_top.mpr hv)
  obtain ⟨t, ht, htl, htr⟩ := live_radius_level_before hU hw z hu huv T hT hR
  rw [radiusLevelTime_eq_of_live_level hU hw z u t htl htr,
    radiusLevelTime_eq_of_live_level hU hw z v T hT hR]
  exact_mod_cast ht

def runningMaxStops {Ω : Type*} (ρ : ℕ → Ω → WithTop ℝ≥0) :
    ℕ → Ω → WithTop ℝ≥0
  | 0 => ρ 0
  | n + 1 => fun ω => max (runningMaxStops ρ n ω) (ρ (n + 1) ω)

lemma runningMaxStops_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (ρ : ℕ → Ω → WithTop ℝ≥0) (hρ : ∀ j, IsStoppingTime ℱ (ρ j)) :
    ∀ j, IsStoppingTime ℱ (runningMaxStops ρ j)
  | 0 => hρ 0
  | j + 1 => (runningMaxStops_stopping ℱ ρ hρ j).max (hρ (j + 1))

lemma runningMaxStops_monotone {Ω : Type*}
    (ρ : ℕ → Ω → WithTop ℝ≥0) (ω : Ω) :
    Monotone (fun j => runningMaxStops ρ j ω) :=
  monotone_nat_of_le_succ (fun _j => le_max_left _ _)

lemma runningMaxStops_eq_of_monotone {Ω : Type*}
    (ρ : ℕ → Ω → WithTop ℝ≥0) (ω : Ω) (hmono : Monotone (fun j => ρ j ω)) :
    ∀ j, runningMaxStops ρ j ω = ρ j ω
  | 0 => rfl
  | j + 1 => by
    change max (runningMaxStops ρ j ω) (ρ (j + 1) ω) = ρ (j + 1) ω
    rw [runningMaxStops_eq_of_monotone ρ ω hmono j,
      max_eq_right (hmono (Nat.le_succ j))]

/-- One increasing stopping sequence represents all prescribed radius
levels simultaneously, including outcomes on which a level is never hit. -/
theorem exists_monotone_radiusLevel_stops
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane)
    (u : ℕ → ℝ) (hu : ∀ j, 0 ≤ u j) (hmono : Monotone u) :
    ∃ τ : ℕ → Ω → WithTop ℝ≥0,
      (∀ j, IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) (τ j)) ∧
      (∀ ω, Monotone (fun j => τ j ω)) ∧
      ∀ᵐ ω ∂P, ∀ j, τ j ω = radiusLevelTime (γ ω) (G ω) z (u j) := by
  let A₀ := logAngleSq κ (initialLogCoordinates z) 0
  have hA₀ : 0 < A₀ := logAngleSq_pos _ _ _
  let ε (n : ℕ) := A₀ / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε₀ (n : ℕ) : ε n ≤ A₀ :=
    div_le_self hA₀.le (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A₀
    simpa only [mul_one_div, mul_zero] using hh
  let a (j n : ℕ) : AngularLocalization B hm κ z (u j) (ε n) :=
    Classical.choice (exists_angularLocalization hB hm hBm hBc hB0 κ hκ hκ8 z (u j)
      (ε n) (hu j) (hε n) (hε₀ n))
  let ρ := fun j => localizedRadiusStop (a j)
  refine ⟨runningMaxStops ρ,
    runningMaxStops_stopping _ ρ (fun j => localizedRadiusStop_stopping (a j)),
    runningMaxStops_monotone ρ, ?_⟩
  filter_upwards [hw] with ω hω
  have he (j : ℕ) : ρ j ω = radiusLevelTime (γ ω) (G ω) z (u j) :=
    localizedRadiusStop_eq_source (a j) hεlim hBc hz ω (γ ω) (G ω) (F ω) hω
  have hρmono : Monotone (fun j => ρ j ω) := by
    intro i j hij
    change ρ i ω ≤ ρ j ω
    rw [he i, he j]
    exact radiusLevelTime_mono ((hBc ω).const_mul _) hω z (hu i) (hmono hij)
  intro j
  rw [runningMaxStops_eq_of_monotone ρ ω hρmono j, he j]

end SLEExactGauge

end

end OAI
