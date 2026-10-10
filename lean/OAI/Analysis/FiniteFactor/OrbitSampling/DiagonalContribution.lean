import OAI.Analysis.FiniteFactor.OrbitSampling.SelfSummability

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

/-- The self-pair part of the empirical squared norm, with its actual P^-2 weight. -/
def sourceSamplingDiagonalContribution (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (θ : SourceCoordinate → ℝ) : ℝ :=
  (∑ n ∈ sourceSamplingPowers stage,
    ∫ x, sourceSamplingProduct stage r b E G n θ x ^ 2
      ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) / ((sourceSamplingPowers stage).card : ℝ)^2

theorem sourceSamplingDiagonalContribution_nonneg (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (θ : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingDiagonalContribution stage r b E G θ :=
  div_nonneg (sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))) (sq_nonneg _)

theorem sourceSamplingProduct_square_integrable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) (n : ℤ) :
    Integrable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) =>
      sourceSamplingProduct stage r b E G n p.1 p.2 ^ 2)
      (sourceAngleLaw.prod (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))) :=
  sampling_square_integrable _ _
    ((max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card)
    (sourceSamplingProduct_measurable stage r b E G hE hG n)
    (fun p => sourceSamplingProduct_bounds stage r b E G n p.1 p.2)

theorem sourceSamplingDiagonalContribution_integrable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    Integrable (sourceSamplingDiagonalContribution stage r b E G) sourceAngleLaw := by
  apply Integrable.div_const
  exact integrable_finsetSum _ (fun n _ =>
    (sourceSamplingProduct_square_integrable stage r b E G hE hG n).integral_prod_left)

/-- The diagonal contribution's expectation is bounded by the proved
summable budget; the finite set is the actual deterministic sample set. -/
theorem sourceSamplingDiagonalContribution_expectation (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (r : Bool) (b : SourceCoordinate → Bool) (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    (∫ θ, sourceSamplingDiagonalContribution stage r b E G θ ∂sourceAngleLaw) ≤ sourceSamplingSelfBudget stage := by
  have hP : (0 : ℝ) < (sourceSamplingPowers stage).card :=
    (Real.rpow_pos_of_pos (sourceBlockSize_pos stage) _).trans_le (sourceSamplingPowers_spec stage hs).2.1
  unfold sourceSamplingDiagonalContribution
  rw [integral_div,integral_finsetSum _ (fun n _ =>
    (sourceSamplingProduct_square_integrable stage r b E G hE hG n).integral_prod_left)]
  have hsum := Finset.sum_le_sum (fun n hn => sourceSamplingProduct_self_moment stage hs r b E G hE hG n hn)
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  calc
    _ ≤ ((sourceSamplingPowers stage).card : ℝ)*
        (2+8*(sourceBlockSize stage : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize stage : ℝ))^(sourceSamplingPrefix stage).card /
        ((sourceSamplingPowers stage).card : ℝ)^2 := div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = _ := by unfold sourceSamplingSelfBudget; field_simp

/-- Actual self-pair expectations are summable across the constructed stages. -/
theorem sourceSamplingDiagonalContribution_summable_integral (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    Summable (fun stage => ∫ θ, sourceSamplingDiagonalContribution stage r b E G θ ∂sourceAngleLaw) := by
  apply sourceSamplingSelfBudget_summable.of_norm_bounded_eventually_nat
  filter_upwards [sourceBlockSize_tendsto.eventually (eventually_ge_atTop 200000)] with stage hs
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (sourceSamplingDiagonalContribution_nonneg stage r b E G))]
  exact sourceSamplingDiagonalContribution_expectation stage hs r b E G hE hG

end
end FiniteFactor

end OAI
