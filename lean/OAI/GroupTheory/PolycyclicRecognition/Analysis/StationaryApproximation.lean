import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationaryCentered
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Compact-uniform stationary coboundary approximations

The Cornulier–Tessera reduced-cohomology theorem gives compact-uniform
coboundary approximation vectors for the zero-mean Hilbert representation.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PolycyclicRecognition

attribute [local instance] stationaryL2Action zeroMeanL2Action

/-- The centered stationary cocycle admits actual ambient L² approximation
vectors, with its mean homomorphism subtracted explicitly. -/
theorem stationary_coboundary_approximation
    {G X W : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
    [MulAction G X] [ContinuousSMul G X]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul G X μ]
    [μ.InnerRegularCompactLTTop]
    (hvan : ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (b : G → Lp W 2 μ) (hbcont : Continuous b) (hb : IsCocycle b)
    {Q : Set G} (hQ : IsCompact Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Lp W 2 μ, ∀ q ∈ Q,
      ‖b q + stationaryPullback μ q φ - φ -
        Lp.const 2 μ (l2MeanSlope μ b hb q).toAdd‖ ≤ ε := by
  have hact (v : ZeroMeanL2 (W := W) μ) : Continuous (fun g : G => g • v) := by
    have h : Continuous (fun g : G => stationaryPullback μ g (v : Lp W 2 μ)) :=
      (continuous_stationaryPullback μ).comp (continuous_id.prodMk continuous_const)
    exact h.subtype_mk _
  obtain ⟨φ, hφ⟩ := hvan (zeroMeanL2_no_fixed μ) hact (centeredL2Cocycle μ b)
    (continuous_centeredL2 μ b hbcont) (isCocycle_centeredL2 μ b hb) Q hQ ε hε
  refine ⟨φ.val, fun q hq => ?_⟩
  have hh := hφ q hq
  change ‖(b q - Lp.const 2 μ (stationaryL2Mean μ (b q))) +
    stationaryPullback μ q φ.val - φ.val‖ ≤ ε at hh
  convert hh using 1
  congr 1
  change b q + stationaryPullback μ q φ.val - φ.val -
    Lp.const 2 μ (stationaryL2Mean μ (b q)) = _
  abel

/-- On a proper metric group, compact-uniform approximations can be chosen
as one sequence using the integer-radius compact exhaustion. -/
theorem coboundary_approximation_sequence
    {G E : Type*} [Group G] [MetricSpace G] [ProperSpace G]
    [NormedAddCommGroup E] [DistribMulAction G E]
    (b : G → E)
    (happrox : ∀ Q : Set G, IsCompact Q → ∀ ε : ℝ, 0 < ε →
      ∃ φ : E, ∀ q ∈ Q, ‖b q + q • φ - φ‖ ≤ ε) :
    ∃ φ : ℕ → E, ∀ Q : Set G, IsCompact Q → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∀ q ∈ Q, ‖b q + q • φ n - φ n‖ ≤ ε := by
  choose φ hφ using fun n : ℕ => happrox (Metric.closedBall (1 : G) n)
    (isCompact_closedBall 1 n) (1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨φ, fun Q hQ ε hε => ?_⟩
  obtain ⟨R, hR⟩ := hQ.isBounded.subset_closedBall (1 : G)
  obtain ⟨N, hN⟩ := exists_nat_ge R
  have heps : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmall := heps.eventually (gt_mem_nhds hε)
  filter_upwards [Filter.eventually_ge_atTop N, hsmall] with n hn hεn
  intro q hq
  refine (hφ n q ?_).trans hεn.le
  exact (Metric.closedBall_subset_closedBall (hN.trans (by exact_mod_cast hn))) (hR hq)

/-- One sequence of ambient approximation vectors works on every compact
set for the stationary cocycle and its actual mean slope. -/
theorem stationary_coboundary_approximation_sequence
    {G X W : Type*} [Group G] [MetricSpace G] [ProperSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
    [MulAction G X] [ContinuousSMul G X]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul G X μ]
    [μ.InnerRegularCompactLTTop]
    (hvan : ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (b : G → Lp W 2 μ) (hbcont : Continuous b) (hb : IsCocycle b) :
    ∃ φ : ℕ → Lp W 2 μ, ∀ Q : Set G, IsCompact Q → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∀ q ∈ Q,
        ‖b q + stationaryPullback μ q (φ n) - φ n -
          Lp.const 2 μ (l2MeanSlope μ b hb q).toAdd‖ ≤ ε := by
  have hact (v : ZeroMeanL2 (W := W) μ) : Continuous (fun g : G => g • v) := by
    exact ((continuous_stationaryPullback μ).comp
      (continuous_id.prodMk continuous_const)).subtype_mk _
  obtain ⟨φ, hφ⟩ := coboundary_approximation_sequence (centeredL2Cocycle μ b)
    (hvan (zeroMeanL2_no_fixed μ) hact (centeredL2Cocycle μ b)
      (continuous_centeredL2 μ b hbcont) (isCocycle_centeredL2 μ b hb))
  refine ⟨fun n => (φ n).val, fun Q hQ ε hε => ?_⟩
  filter_upwards [hφ Q hQ ε hε] with n hn
  intro q hq
  have hh := hn q hq
  change ‖(b q - Lp.const 2 μ (stationaryL2Mean μ (b q))) +
    stationaryPullback μ q (φ n).val - (φ n).val‖ ≤ ε at hh
  convert hh using 1
  congr 1
  change b q + stationaryPullback μ q (φ n).val - (φ n).val -
    Lp.const 2 μ (stationaryL2Mean μ (b q)) = _
  abel

/-- The squared extended norm integral of an L² vector is its squared norm. -/
theorem lintegral_enorm_sq_L2 {X W : Type*} [MeasurableSpace X]
    [NormedAddCommGroup W] (μ : Measure X) (f : Lp W 2 μ) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ENNReal.ofReal ‖f‖ ^ 2 := by
  have h := congrArg (fun r : ℝ≥0∞ => r ^ (2 : ℝ))
    (eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (Lp.aestronglyMeasurable f))
  simp only [ENNReal.toReal_ofNat, ← ENNReal.rpow_mul, one_div,
    inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one] at h
  rw [← Lp.enorm_def, ← ofReal_norm] at h
  simpa only [ENNReal.rpow_ofNat] using h.symm

end PolycyclicRecognition

end

end OAI
