import OAI.GroupTheory.PolycyclicRecognition.Algebra.OccupationLimitSelection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.OccupationMicrostepLimit

namespace OAI

/-! # The stationary integral in the integer microstep estimate -/

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory Metric
open scoped Topology NNReal

/-- Restrict the stationary real-time estimate to integer times and put
it into the real integral form used by the dominated microstep argument. -/
theorem stationary_integral_microsteps
    {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
    [IsTopologicalGroup G] [IsIsometricSMul G G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd))
    (d : ℝ → G) (S : Set W) (μ : Measure (NormalizedPair G Λ))
    (hstat : Tendsto (fun r : ℝ => ∫⁻ p,
      ENNReal.ofReal (infDist (r⁻¹ • pairHeight π (d r) p) S) ∂μ) atTop (𝓝 0)) :
    Tendsto (fun L : ℕ => ∫ p,
      infDist ((L : ℝ)⁻¹ • pairHeight π (d L) p) S ∂μ) atTop (𝓝 0) := by
  let f : ℕ → C(NormalizedPair G Λ, ℝ) := fun L =>
    ⟨_, continuous_pair_label_distance π hπ (d L) L S⟩
  exact integral_tendsto_zero_of_lintegral_nonneg μ f (fun _ _ => infDist_nonneg)
    (hstat.comp tendsto_natCast_atTop_atTop)

end PolycyclicRecognition

end

end OAI
