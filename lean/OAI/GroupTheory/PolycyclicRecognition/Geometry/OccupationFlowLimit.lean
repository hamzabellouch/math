import OAI.GroupTheory.PolycyclicRecognition.Geometry.OccupationFlowMicrosteps

namespace OAI

/-! # Convex flow increments from dominated occupation laws -/

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory Metric Set
open scoped Topology NNReal

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ K : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- For a genuine continuous one-parameter subgroup all mesh, remainder,
and endpoint hypotheses follow from the flow laws. Only the occupation
comparison and the stationary estimate remain to be supplied. -/
theorem normalized_flow_error_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (π : G →* Multiplicative W) (hπ : LipschitzWith K (fun g => (π g).toAdd))
    (σ μs : ι → ProbabilityMeasure (NormalizedPair G Λ))
    (μ : ProbabilityMeasure (NormalizedPair G Λ)) (hμ : Tendsto μs l (𝓝 μ))
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (t : ι → ℝ) (ht : Tendsto t l atTop) (c : ℝ≥0)
    (hdom : ∀ L : ℕ, 0 < L → ∀ᶠ i in l, ∀ j : Fin ⌊t i / (L : ℝ)⌋₊,
      Measure.map (fun p : NormalizedPair G Λ => (d L ^ (j : ℕ))⁻¹ • p)
        (σ i : Measure _) ≤ c • (μs i : Measure _))
    {S : Set W} (hS : IsCompact S) {w₀ : W} (hw₀ : w₀ ∈ S)
    (hstationary : Tendsto (fun L : ℕ => ∫ p : NormalizedPair G Λ,
      infDist ((L : ℝ)⁻¹ • pairHeight π (d L) p) S ∂(μ : Measure _)) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ p : NormalizedPair G Λ,
      infDist ((t i)⁻¹ • pairHeight π (d (t i)) p) (convexHull ℝ S)
        ∂(σ i : Measure _)) l (𝓝 0) := by
  obtain ⟨D, hD, hb⟩ := exists_flow_microstep_bound d hd hd0 hmul
  apply normalized_microstep_error_tendsto_zero π hπ σ μs μ hμ t ht
    (fun i => d (t i)) (fun L => d L)
    (fun L i => ⌊t i / (L : ℝ)⌋₊)
    (fun L i => d (t i - (⌊t i / (L : ℝ)⌋₊ : ℝ) * L)) c hD _ hS hw₀ hstationary
  intro L hL
  filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℝ)), hdom L hL] with i hi hid
  obtain ⟨hlo, hhi, hrem, hend⟩ := hb L hL (t i) hi
  exact ⟨hi, hlo, hhi, hrem, hend, hid⟩

end PolycyclicRecognition

end

end OAI
