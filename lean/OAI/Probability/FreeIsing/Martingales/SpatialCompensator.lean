import OAI.Probability.FreeIsing.Estimates.CompensatedSquareLimit
import OAI.Probability.FreeIsing.Estimates.NonnegativeSeriesL1
import OAI.Probability.FreeIsing.Martingales.PredictableL2Completion
import OAI.Probability.FreeIsing.Stochastic.StoppedBrownianArraySquare

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem367.MartingaleSpatialCompensator

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {F : Filtration ℝ≥0 mΩ}

theorem spatial_sum_compensatedSquare_martingale [Countable ι]
    {X A : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hX2 : ∀ i t, MemLp (X i t) 2 μ)
    (hdiag : ∀ i, Martingale (fun t ω => X i t ω ^ 2 - A i t ω) F μ)
    (hcross : Pairwise fun i j => Martingale (fun t ω => X i t ω * X j t ω) F μ)
    (hAad : ∀ i, StronglyAdapted F (A i))
    (hAint : ∀ i t, Integrable (A i t) μ)
    (hAnonneg : ∀ i t ω, 0 ≤ A i t ω)
    (hAsum : ∀ t, Summable (fun i => ∫ ω, A i t ω ∂μ))
    (hYad : StronglyAdapted F Y) (hY2 : ∀ t, MemLp (Y t) 2 μ)
    (hYsum : ∀ t, HasSum (fun i => (hX2 i t).toLp (X i t)) ((hY2 t).toLp (Y t))) :
    Martingale (fun t ω => Y t ω ^ 2 - ∑' i, A i t ω) F μ := by
  classical
  apply CompensatedSquareLimit.martingale_compensatedSquare_of_limits
    (l := (atTop : Filter (Finset ι)))
    (X := fun s t ω => ∑ i ∈ s, X i t ω)
    (A := fun s t ω => ∑ i ∈ s, A i t ω)
  · intro s t
    exact memLp_finsetSum s (fun i _ => hX2 i t)
  · intro s t
    exact integrable_finsetSum s (fun i _ => hAint i t)
  · exact StoppedBrownianArraySquare.finite_sum_compensated_square_martingale X A hdiag hcross
  · exact hYad
  · exact hY2
  · intro t
    let : MeasurableSpace Ω := F t
    exact StronglyMeasurable.tsum (fun i => hAad i t)
  · intro t
    exact (NonnegativeSeriesL1.integrable_tsum_of_nonnegative
      (fun i => hAint i t) (fun i ω => hAnonneg i t ω) (hAsum t)).2.1
  · intro t
    apply CompensatedSquareLimit.tendsto_eLpNorm_two_of_meanSquare
      (fun s => memLp_finsetSum s (fun i _ => hX2 i t)) (hY2 t)
    exact PredictableL2.tendsto_integral_sq_error_of_hasSum
      (fun i => X i t) (fun i => hX2 i t) (hY2 t) (hYsum t)
  · intro t
    exact NonnegativeSeriesL1.tendsto_finsetSum_L1_of_nonnegative
      (fun i => hAint i t) (fun i ω => hAnonneg i t ω) (hAsum t)

end Problem367.MartingaleSpatialCompensator

end

end OAI
