import OAI.GroupTheory.PolycyclicRecognition.Algebra.OccupationMicrosteps
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

/-! # The two successive limits in the convex increment argument -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Metric Set
open scoped NNReal Topology

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ K : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- First take the chart scale to infinity for a fixed integer microstep,
then take the microstep length to infinity for the single limiting law.
No rate of stationary convergence uniform over probabilities is used. -/
theorem normalized_microstep_error_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (π : G →* Multiplicative W) (hπ : LipschitzWith K (fun g => (π g).toAdd))
    (σ μs : ι → ProbabilityMeasure (NormalizedPair G Λ))
    (μ : ProbabilityMeasure (NormalizedPair G Λ))
    (hμ : Tendsto μs l (𝓝 μ))
    (t : ι → ℝ) (ht : Tendsto t l atTop)
    (endpoint : ι → G) (g : ℕ → G) (n : ℕ → ι → ℕ) (h : ℕ → ι → G)
    (c : ℝ≥0) {D : ℝ} (hD : 0 ≤ D)
    (hsteps : ∀ L : ℕ, 0 < L → ∀ᶠ r in l,
      0 < t r ∧ (n L r : ℝ) * L ≤ t r ∧ t r ≤ ((n L r : ℝ) + 1) * L ∧
      dist 1 (h L r) ≤ D * L ∧ g L ^ n L r * h L r = endpoint r ∧
      ∀ j : Fin (n L r), Measure.map
        (fun p : NormalizedPair G Λ => (g L ^ (j : ℕ))⁻¹ • p) (σ r : Measure _) ≤
          c • (μs r : Measure _))
    {S : Set W} (hS : IsCompact S) {w₀ : W} (hw₀ : w₀ ∈ S)
    (hstationary : Tendsto (fun L : ℕ => ∫ p : NormalizedPair G Λ,
      infDist ((L : ℝ)⁻¹ • pairHeight π (g L) p) S ∂(μ : Measure _)) atTop (𝓝 0)) :
    Tendsto (fun r => ∫ p : NormalizedPair G Λ,
      infDist ((t r)⁻¹ • pairHeight π (endpoint r) p) (convexHull ℝ S)
        ∂(σ r : Measure _)) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun r => ha.trans_le (integral_nonneg (fun _ => infDist_nonneg)))
  · intro b hb
    have hstat := hstationary.const_mul (c : ℝ)
    simp only [mul_zero] at hstat
    have hsmall := hstat.eventually (eventually_lt_nhds (half_pos hb))
    obtain ⟨L, hL, hLb⟩ := ((eventually_gt_atTop (0 : ℕ)).and hsmall).exists
    let dL : C(NormalizedPair G Λ, ℝ) :=
      ⟨fun p => infDist ((L : ℝ)⁻¹ • pairHeight π (g L) p) S,
        continuous_pair_label_distance π hπ.continuous (g L) L S⟩
    have hint := (ProbabilityMeasure.continuous_integral_continuousMap dL).tendsto μ |>.comp hμ
    have hrem : Tendsto (fun r => ((L : ℝ) / t r) *
        ((K : ℝ) * Λ * D + ‖w₀‖)) l (𝓝 0) := by
      simpa only [zero_mul] using
        (tendsto_const_nhds.div_atTop ht).mul_const ((K : ℝ) * Λ * D + ‖w₀‖)
    have hrhs := (hint.const_mul (c : ℝ)).add hrem
    simp only [add_zero] at hrhs
    have hrhsb := hrhs.eventually (eventually_lt_nhds (hLb.trans (half_lt_self hb)))
    filter_upwards [hsteps L hL, hrhsb] with r hs hlt
    obtain ⟨htr, hn, hn', hremr, hend, hdom⟩ := hs
    have he := integral_normalized_microsteps_le (Λ := Λ) (K := K) (c := c)
      (σ r : Measure (NormalizedPair G Λ)) (μs r : Measure (NormalizedPair G Λ))
      π hπ (g L) (h L r) (n L r) hdom (Nat.cast_pos.mpr hL) htr hD
      hn hn' hremr hS hw₀
    rw [hend] at he
    exact he.trans_lt hlt

end PolycyclicRecognition

end

end OAI
