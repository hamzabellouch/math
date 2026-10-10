import OAI.Geometry.RCD.Metric.ConcentratedTimeLimit
import OAI.Geometry.RCD.Harmonic.RadialContractionFactor

namespace OAI

/-! # Radial plans with the small-time CD density bound

The terminal laws are actual normalized balls shrinking to the pole.
The one-sided source bound remains uniform and passes to the limit.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.exists_radial_time_plan {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {κ : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K) (ν₀ : ProbabilityMeasure X)
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (h0 : (ν₀ : Measure X) ≤ C₀ • hausdorff n X)
    (p : X) {R D : ℝ} (hR : 0 < R) (hRD : R < D)
    (hs0 : ∀ᵐ x ∂(ν₀ : Measure X), dist x p ≤ R)
    (t : Time) (ht1 : (t : ℝ) < 1) :
    ∃ π : ProbabilityMeasure C(Time, X),
      (∀ᵐ γ ∂(π : Measure C(Time, X)), IsGeodesic γ ∧ ∀ s, dist (γ s) p ≤ 3 * D) ∧
      π.map (fun γ => γ 0) = ν₀ ∧
      π.map (fun γ => γ 1) = (⟨Measure.dirac p, inferInstance⟩ : ProbabilityMeasure X) ∧
      (π.map (fun γ => γ t) : Measure X) ≤
        (C₀ * ENNReal.ofReal (radialContractionDensity n κ D t)) • hausdorff n X := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let ε (k : ℕ) : ℝ := (D - R) / ((k : ℝ) + 1)
  have hDR : 0 < D - R := sub_pos.mpr hRD
  have hD : 0 < D := hR.trans hRD
  have hε (k : ℕ) : 0 < ε k := div_pos hDR (by positivity)
  have hεle (k : ℕ) : ε k ≤ D - R := by
    apply (div_le_iff₀ (show 0 < (k : ℝ) + 1 by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, div_eq_mul_inv, one_div, one_mul, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (D - R)
  have hball0 (k : ℕ) : μ (ball p (ε k)) ≠ 0 := (hX.fullSupport p (ε k) (hε k)).ne'
  have hballtop (k : ℕ) : μ (ball p (ε k)) ≠ ∞ :=
    (hX.finiteOnBounded _ isBounded_ball).ne
  let ν (k : ℕ) : ProbabilityMeasure X :=
    ⟨uniformOn μ (ball p (ε k)), uniformOn_probability μ _ (hball0 k) (hballtop k)⟩
  have hsν (k : ℕ) : ∀ᵐ x ∂(ν k : Measure X), dist x p ≤ ε k :=
    (uniformOn_ae_mem μ (ball p (ε k)) measurableSet_ball).mono fun _ hx => hx.le
  have hνlim := probability_tendsto_dirac_of_radius hεlim hsν
  have hC : C₀ * ENNReal.ofReal (radialContractionDensity n κ D t) ≠ ∞ :=
    ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top
  apply exists_concentrated_time_limit μ p (by positivity : 0 ≤ 3 * D) t ν₀ ν hνlim hC
  intro k
  have h1 : (ν k : Measure X) ≤ (μ (ball p (ε k)))⁻¹ • μ := by
    intro A
    exact mul_le_mul_right (Measure.restrict_le_self (μ := μ) (s := ball p (ε k)) A) _
  have hs0D : ∀ᵐ x ∂(ν₀ : Measure X), dist x p ≤ D :=
    hs0.mono fun _ hx => hx.trans hRD.le
  have hsk : ∀ᵐ x ∂(ν k : Measure X), dist x p ≤ D :=
    (hsν k).mono fun _ hx => by linarith [hεle k]
  have hβ : ∀ x ∈ closedBall p R, ∀ y ∈ closedBall p (ε k),
      radialContractionFloor n κ D t ≤ tau K n (1 - (t : ℝ)) (dist x y) := by
    intro x hx y hy
    apply radialContractionFloor_le_tau hn hκ hK dist_nonneg _ t.2.1 t.2.2
    have hxy := dist_triangle x p y
    rw [dist_comm p y] at hxy
    change dist x p ≤ R at hx
    change dist y p ≤ ε k at hy
    linarith [hεle k]
  obtain ⟨π, hπ, hg, hp, hm⟩ := hX.exists_time_compression hn (ν₀ : Measure X)
    (ν k : Measure X) hC₀ (ENNReal.inv_ne_top.mpr (hball0 k)) h0 h1 p hD.le hs0D hsk
    t (radialContractionFloor_pos n κ D ht1).ne' (radialContractionFloor_ne_top n κ D t)
    (closedBall p R) (closedBall p (ε k)) hs0 (hsν k) hβ
  let := hπ
  have he := optimalPlan_endpoints (ν₀ : Measure X) (ν k : Measure X) π hp
  refine ⟨⟨π, hπ⟩, optimal_geodesic_plan_bounded _ _ π hg hp p hD.le hs0D hsk, ?_, ?_, ?_⟩
  · apply Subtype.ext
    exact he.1
  · apply Subtype.ext
    exact he.2
  · change π.map (fun γ => γ t) ≤ _
    simpa only [div_eq_mul_inv, radialContractionFloor_inv_pow (by omega : 0 < n) κ D ht1]
      using hm

end RegularPointCoordinates

end OAI
