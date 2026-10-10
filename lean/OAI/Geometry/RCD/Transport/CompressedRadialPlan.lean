import OAI.Geometry.RCD.Transport.RadialMidpoint
import OAI.Geometry.RCD.Transport.OptimalRadialMidpoint

namespace OAI

/-! # A bounded-compression radial plan from an actual bounded density

First construct the radial midpoint by endpoint concentration. Apply the
proved bounded-compression transport theorem to that midpoint. Optimal
cost rigidity forces the replacement to have exactly the radial speed.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.exists_compressed_radial_plan {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (ν₀ : ProbabilityMeasure X)
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (h0 : (ν₀ : Measure X) ≤ C₀ • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 < R)
    (hs0 : ∀ᵐ x ∂(ν₀ : Measure X), dist x p ≤ R) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      π.map (fun γ => γ 0) = (ν₀ : Measure X) ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π ∧
      (∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X) ∧
      ∀ᵐ γ ∂π, dist (γ 0) (γ 1) = dist (γ 1) p ∧
        dist (γ 0) p = dist (γ 0) (γ 1) + dist (γ 1) p := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  obtain ⟨q, hq, hq0, hq1, hqm⟩ := hX.exists_radial_midpoint_plan hn ν₀ hC₀ h0 p hR hs0
  let η : Measure X := (q.map (fun γ => γ midpointTime) : Measure X)
  let C₁ := C₀ / (midpointFloor K n (2 * R)) ^ n
  have hC₁ : C₁ ≠ ∞ :=
    ENNReal.div_ne_top hC₀ (pow_ne_zero _ (midpointFloor_pos K n (2 * R)).ne')
  let A := max C₀ C₁
  have hA : A ≠ ∞ := (max_lt_iff.mpr ⟨hC₀.lt_top, hC₁.lt_top⟩).ne
  have hb0 : (ν₀ : Measure X) ≤ A • μ := by
    intro S
    exact (h0 S).trans (mul_le_mul_left (le_max_left C₀ C₁) (μ S))
  have hb1 : η ≤ A • μ := by
    intro S
    exact (hqm S).trans (mul_le_mul_left (le_max_right C₀ C₁) (μ S))
  have hη : ∀ᵐ x ∂η, dist x p ≤ 3 * R := by
    change ∀ᵐ x ∂(q.map (fun γ => γ midpointTime) : Measure X), dist x p ≤ 3 * R
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable
      (measurableSet_le (measurable_id.dist measurable_const) measurable_const)).mpr
    exact hq.mono fun _ hγ => hγ.2 midpointTime
  have hs0' : ∀ᵐ x ∂(ν₀ : Measure X), dist x p ≤ 3 * R :=
    hs0.mono fun _ hx => by linarith
  obtain ⟨π, hπ, hg, hp, hi, hcomp⟩ := hX.exists_bounded_entropy_plan K n hn
    (ν₀ : Measure X) η hA hb0 hb1 p (by positivity : 0 ≤ 3 * R) hs0' hη
  let := hπ
  have hqD : Integrable (fun γ : C(Time, X) => dist (γ 0) (γ 1) ^ 2)
      (q : Measure C(Time, X)) := by
    apply Integrable.mono' (integrable_const ((6 * R) ^ 2))
      (((measurable_path_eval 0).dist (measurable_path_eval 1)).pow_const 2).aestronglyMeasurable
    filter_upwards [hq] with γ hγ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have htri := dist_triangle (γ 0) p (γ 1)
    rw [dist_comm p (γ 1)] at htri
    exact pow_le_pow_left₀ dist_nonneg (by linarith [hγ.2 0, hγ.2 1]) 2
  have hqfinite : transportCost ((q : Measure C(Time, X)).map (fun γ => (γ 0, γ 1))) ≠ ∞ := by
    rw [transportCost_plan_eq_integral _ hqD]
    exact ENNReal.ofReal_ne_top
  have hq1' : (q : Measure C(Time, X)).map (fun γ => γ 1) = Measure.dirac p := by
    have hh := congrArg (fun ν : ProbabilityMeasure X => (ν : Measure X)) hq1
    change (q.map (fun γ => γ 1) : Measure X) = Measure.dirac p at hh
    simpa only [ProbabilityMeasure.toMeasure_map] using hh
  have hq0' : (q : Measure C(Time, X)).map (fun γ => γ 0) = (ν₀ : Measure X) := by
    have hh := congrArg (fun ν : ProbabilityMeasure X => (ν : Measure X)) hq0
    simpa only [ProbabilityMeasure.toMeasure_map] using hh
  have hp' : IsOptimalCoupling ((q : Measure C(Time, X)).map (fun γ => γ 0))
      ((q : Measure C(Time, X)).map (fun γ => γ midpointTime))
      (π.map (fun γ => (γ 0, γ 1))) := by
    rw [hq0']
    exact hp
  refine ⟨π, hπ, compressionBudget K n (2 * (3 * R)) A,
    compressionBudget_ne_top K n _ hA, (optimalPlan_endpoints _ _ π hp).1, hg,
    (memLp_two_iff_integrable_sq
      ((measurable_path_eval 0).dist (measurable_path_eval 1)).aestronglyMeasurable).mpr hi,
    fun t => (hcomp t).1, ?_⟩
  exact optimal_radial_midpoint q p (hq.mono fun _ hγ => hγ.1) hq1' hqfinite π hp'

end RegularPointCoordinates

end OAI
