import OAI.Geometry.RCD.Metric.ConcentratingProbability
import OAI.Geometry.RCD.Transport.AsymmetricMidpointCapacity

namespace OAI

/-! # A radial limiting plan whose midpoint retains bounded density

Only midpoint compression is imposed before the endpoint concentrates.
Compactness of the actual bounded geodesic plans retains the initial law,
the Dirac final law, and the same midpoint density bound.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem exists_concentrated_midpoint_limit (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (p : X) {R : ℝ} (hR : 0 ≤ R) (ν₀ : ProbabilityMeasure X)
    (ν : ℕ → ProbabilityMeasure X)
    (hν : Tendsto ν atTop (𝓝 (⟨Measure.dirac p, inferInstance⟩ : ProbabilityMeasure X)))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hplans : ∀ k, ∃ π : ProbabilityMeasure C(Time, X),
      (∀ᵐ γ ∂(π : Measure C(Time, X)), IsGeodesic γ ∧ ∀ t, dist (γ t) p ≤ R) ∧
      π.map (fun γ => γ 0) = ν₀ ∧ π.map (fun γ => γ 1) = ν k ∧
      (π.map (fun γ => γ midpointTime) : Measure X) ≤ C • μ) :
    ∃ π : ProbabilityMeasure C(Time, X),
      (∀ᵐ γ ∂(π : Measure C(Time, X)), IsGeodesic γ ∧ ∀ t, dist (γ t) p ≤ R) ∧
      π.map (fun γ => γ 0) = ν₀ ∧
      π.map (fun γ => γ 1) = (⟨Measure.dirac p, inferInstance⟩ : ProbabilityMeasure X) ∧
      (π.map (fun γ => γ midpointTime) : Measure X) ≤ C • μ := by
  classical
  choose π hgeo h₀ h₁ hmid using hplans
  obtain ⟨q, hq, t, ht, hlim⟩ := (isCompact_bounded_geodesic_plans p hR).tendsto_subseq hgeo
  have he₀ : q.map (fun γ => γ 0) = ν₀ := by
    apply tendsto_nhds_unique ((ProbabilityMeasure.continuous_map (continuous_eval_const 0)).tendsto q |>.comp hlim)
    simpa only [Function.comp_def, h₀] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => ν₀) atTop (𝓝 ν₀))
  have he₁ : q.map (fun γ => γ 1) = (⟨Measure.dirac p, inferInstance⟩ : ProbabilityMeasure X) := by
    apply tendsto_nhds_unique ((ProbabilityMeasure.continuous_map (continuous_eval_const 1)).tendsto q |>.comp hlim)
    simpa only [Function.comp_def, h₁] using hν.comp ht.tendsto_atTop
  let W := closedBall p R
  let : IsFiniteMeasure (μ.restrict W) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall p R).measure_lt_top (μ := μ)⟩
  have hc : IsClosed {η : ProbabilityMeasure X | (η : Measure X) ≤ C • μ.restrict W} := by
    convert (lowerSemicontinuous_transportExcessMass (μ.restrict W) hC).isClosed_preimage 0 using 1
    ext η
    simp only [mem_ofPred_eq, mem_preimage, mem_Iic, nonpos_iff_eq_zero,
      transportExcessMass_zero_iff (μ.restrict W) (η : Measure X) hC]
  have hs (k : ℕ) : ∀ᵐ x ∂((π k).map (fun γ => γ midpointTime) : Measure X), x ∈ W := by
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable measurableSet_closedBall).mpr
    filter_upwards [hgeo k] with γ hγ
    exact hγ.2 midpointTime
  have hbound : ∀ k, ((π k).map (fun γ => γ midpointTime) : Measure X) ≤ C • μ.restrict W :=
    fun k => (compression_iff_localized μ _ (hs k) C).mp (hmid k)
  have hqm : (q.map (fun γ => γ midpointTime) : Measure X) ≤ C • μ.restrict W := by
    apply hc.mem_of_tendsto ((ProbabilityMeasure.continuous_map
      (continuous_eval_const midpointTime)).tendsto q |>.comp hlim)
    exact Eventually.of_forall fun k => hbound (t k)
  refine ⟨q, hq, he₀, he₁, hqm.trans ?_⟩
  intro A
  change C * (μ.restrict W) A ≤ C * μ A
  exact mul_le_mul_right (Measure.restrict_le_self (μ := μ) (s := W) A) C

end RegularPointCoordinates

end OAI
