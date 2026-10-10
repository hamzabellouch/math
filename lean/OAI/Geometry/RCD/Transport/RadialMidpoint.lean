import OAI.Geometry.RCD.Transport.ConcentratedMidpointLimit

namespace OAI

/-! # A radial transport plan with a controlled midpoint

The second marginal is constructed by normalized balls shrinking to the
pole. The asymmetric CD estimate controls the midpoint independently of
those ball densities; compactness then gives the actual Dirac endpoint.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.exists_radial_midpoint_plan {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (ν₀ : ProbabilityMeasure X)
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (h0 : (ν₀ : Measure X) ≤ C₀ • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 < R)
    (hs0 : ∀ᵐ x ∂(ν₀ : Measure X), dist x p ≤ R) :
    ∃ π : ProbabilityMeasure C(Time, X),
      (∀ᵐ γ ∂(π : Measure C(Time, X)), IsGeodesic γ ∧ ∀ t, dist (γ t) p ≤ 3 * R) ∧
      π.map (fun γ => γ 0) = ν₀ ∧
      π.map (fun γ => γ 1) = (⟨Measure.dirac p, inferInstance⟩ : ProbabilityMeasure X) ∧
      (π.map (fun γ => γ midpointTime) : Measure X) ≤
        (C₀ / (midpointFloor K n (2 * R)) ^ n) • hausdorff n X := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let ε (k : ℕ) : ℝ := R / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := div_pos hR (by positivity)
  have hεle (k : ℕ) : ε k ≤ R := by
    apply (div_le_iff₀ (show 0 < (k : ℝ) + 1 by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, div_eq_mul_inv, one_div, one_mul, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul R
  have hball0 (k : ℕ) : μ (ball p (ε k)) ≠ 0 := (hX.fullSupport p (ε k) (hε k)).ne'
  have hballtop (k : ℕ) : μ (ball p (ε k)) ≠ ∞ :=
    (hX.finiteOnBounded _ isBounded_ball).ne
  let ν (k : ℕ) : ProbabilityMeasure X :=
    ⟨uniformOn μ (ball p (ε k)), uniformOn_probability μ _ (hball0 k) (hballtop k)⟩
  have hsν (k : ℕ) : ∀ᵐ x ∂(ν k : Measure X), dist x p ≤ ε k :=
    (uniformOn_ae_mem μ (ball p (ε k)) measurableSet_ball).mono fun _ hx => hx.le
  have hνlim := probability_tendsto_dirac_of_radius hεlim hsν
  have hC : C₀ / (midpointFloor K n (2 * R)) ^ n ≠ ∞ :=
    ENNReal.div_ne_top hC₀ (pow_ne_zero _ (midpointFloor_pos K n (2 * R)).ne')
  apply exists_concentrated_midpoint_limit μ p (by positivity : 0 ≤ 3 * R) ν₀ ν hνlim hC
  intro k
  have h1 : (ν k : Measure X) ≤ (μ (ball p (ε k)))⁻¹ • μ := by
    intro A
    exact mul_le_mul_right (Measure.restrict_le_self (μ := μ) (s := ball p (ε k)) A) _
  have hsk : ∀ᵐ x ∂(ν k : Measure X), dist x p ≤ R :=
    (hsν k).mono fun _ hx => hx.trans (hεle k)
  obtain ⟨π, hπ, hg, hp, hm⟩ := hX.exists_asymmetric_midpoint hn (ν₀ : Measure X)
    (ν k : Measure X) hC₀ (ENNReal.inv_ne_top.mpr (hball0 k)) h0 h1 p hR.le hs0 hsk
  let := hπ
  have he := optimalPlan_endpoints (ν₀ : Measure X) (ν k : Measure X) π hp
  refine ⟨⟨π, hπ⟩, optimal_geodesic_plan_bounded _ _ π hg hp p hR.le hs0 hsk, ?_, ?_, ?_⟩
  · apply Subtype.ext
    exact he.1
  · apply Subtype.ext
    exact he.2
  · change π.map (fun γ => γ midpointTime) ≤ _
    apply hm.trans
    intro A
    exact mul_le_mul_left (midpointSupportFactor_inv_le K (by omega : 0 < n) (2 * R)
      C₀ ((μ (ball p (ε k)))⁻¹)) (μ A)

end RegularPointCoordinates

end OAI
