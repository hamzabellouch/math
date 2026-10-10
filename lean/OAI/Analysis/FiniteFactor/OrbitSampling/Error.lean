import OAI.Analysis.FiniteFactor.OrbitSampling.ProductError
import OAI.Analysis.FiniteFactor.OrbitSampling.DiagonalEvent
import OAI.Analysis.FiniteFactor.Sampling.Cancellation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

def sourceSamplingEmpiricalDensity (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (θ x : SourceCoordinate → ℝ) : ℝ :=
  (∑ n ∈ sourceSamplingPowers stage, sourceSamplingProduct stage r b E G n θ x)/
    ((sourceSamplingPowers stage).card : ℝ)

/-- The full sampling error, including every distinct-pair and mixed term. -/
def sourceSamplingSquaredError (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (θ : SourceCoordinate → ℝ) : ℝ :=
  ∫ x, (sourceSamplingEmpiricalDensity stage r b E G θ x-sourceSamplingIdealDensity stage r b E G x)^2
    ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)

theorem sourceSampling_error_joint_integrable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    Integrable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) =>
      (sourceSamplingEmpiricalDensity stage r b E G p.1 p.2-sourceSamplingIdealDensity stage r b E G p.2)^2)
      (sourceAngleLaw.prod (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))) := by
  apply sampling_average_square_integrable
  · intro n _ k _
    exact sourceSamplingProduct_pair_integrable stage r b E G hE hG n k
  · intro n _
    exact sourceSamplingProduct_mixed_integrable stage r b E G hE hG n
  · have hm : Measurable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) => sourceSamplingIdealDensity stage r b E G p.2) :=
      (sourceSamplingIdealDensity_measurable stage r b E G hE hG).comp measurable_snd
    have hi := sampling_bounded_product_integrable
      (sourceAngleLaw.prod (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)))
      (fun p => sourceSamplingIdealDensity stage r b E G p.2) (fun p => sourceSamplingIdealDensity stage r b E G p.2)
      hm hm _ (fun p => sourceSamplingIdealDensity_bounds stage r b E G hE hG p.2)
      (fun p => sourceSamplingIdealDensity_bounds stage r b E G hE hG p.2)
    simpa only [pow_two] using hi

theorem sourceSamplingSquaredError_integrable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    Integrable (sourceSamplingSquaredError stage r b E G) sourceAngleLaw :=
  (sourceSampling_error_joint_integrable stage r b E G hE hG).integral_prod_left

theorem sourceSamplingSquaredError_measurable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    Measurable (sourceSamplingSquaredError stage r b E G) := by
  have hm : Measurable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) =>
      sourceSamplingEmpiricalDensity stage r b E G p.1 p.2) :=
    (Finset.measurable_sum _ (fun n _ => sourceSamplingProduct_measurable stage r b E G hE hG n)).div_const _
  exact ((hm.sub ((sourceSamplingIdealDensity_measurable stage r b E G hE hG).comp measurable_snd)).pow_const 2).stronglyMeasurable.integral_prod_right.measurable

theorem sourceSamplingSquaredError_nonneg (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (θ : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingSquaredError stage r b E G θ := integral_nonneg (fun _ => sq_nonneg _)

/-- Full expected squared sampling error with the source's actual sample set,
weights and ideal density. All distinct-pair and mixed assumptions are proved. -/
theorem sourceSamplingSquaredError_expectation (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (r : Bool) (b : SourceCoordinate → Bool) (a c a' c' : SourceCoordinate → ℝ) :
    (∫ θ, sourceSamplingSquaredError stage r b (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ ∂sourceAngleLaw) ≤
      (∫ θ, sourceSamplingDiagonalContribution stage r b (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ ∂sourceAngleLaw)+
      3*sourceSamplingCorrelationBudget stage := by
  let E := fun i => Set.Icc (a i) (c i)
  let G := fun i => Set.Icc (a' i) (c' i)
  have hE : ∀ i, MeasurableSet (E i) := fun _ => measurableSet_Icc
  have hG : ∀ i, MeasurableSet (G i) := fun _ => measurableSet_Icc
  let μ := sourceAngleLaw.prod (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))
  let S := sourceSamplingPowers stage
  let f (n : ℤ) (p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)) := sourceSamplingProduct stage r b E G n p.1 p.2
  let g (p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)) := sourceSamplingIdealDensity stage r b E G p.2
  have hpair (n k : ℤ) : Integrable (fun p => f n p*f k p) μ :=
    sourceSamplingProduct_pair_integrable stage r b E G hE hG n k
  have hmix (n : ℤ) : Integrable (fun p => f n p*g p) μ :=
    sourceSamplingProduct_mixed_integrable stage r b E G hE hG n
  have hg : Integrable (fun p => g p^2) μ := by
    have hm : Measurable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) => sourceSamplingIdealDensity stage r b E G p.2) :=
      (sourceSamplingIdealDensity_measurable stage r b E G hE hG).comp measurable_snd
    simpa only [pow_two] using sampling_bounded_product_integrable μ g g hm hm _
      (fun p => sourceSamplingIdealDensity_bounds stage r b E G hE hG p.2)
      (fun p => sourceSamplingIdealDensity_bounds stage r b E G hE hG p.2)
  have hA : (∫ p, g p^2 ∂μ) = ∫ x, sourceSamplingIdealDensity stage r b E G x^2
      ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) := by
    rw [integral_prod _ hg]
    simp [g]
  have hB (n k : ℤ) : (∫ p, f n p*f k p ∂μ) =
      ∫ θ, ∫ x, sourceSamplingProduct stage r b E G n θ x*sourceSamplingProduct stage r b E G k θ x
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) ∂sourceAngleLaw := integral_prod _ (hpair n k)
  have hM (n : ℤ) : (∫ p, f n p*g p ∂μ) =
      ∫ θ, ∫ x, sourceSamplingProduct stage r b E G n θ x*sourceSamplingIdealDensity stage r b E G x
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) ∂sourceAngleLaw := integral_prod _ (hmix n)
  have hS : S.Nonempty := by
    have hP : (0 : ℝ) < (sourceSamplingPowers stage).card :=
      (Real.rpow_pos_of_pos (sourceBlockSize_pos stage) _).trans_le (sourceSamplingPowers_spec stage hs).2.1
    exact Finset.card_pos.mp (by exact_mod_cast hP)
  have hc := sampling_finite_cancellation S hS
    (fun n k => ∫ p, f n p*f k p ∂μ) (fun n => ∫ p, f n p*g p ∂μ)
    (∫ p, g p^2 ∂μ) (sourceSamplingCorrelationBudget stage)
    (integral_nonneg (fun _ => sq_nonneg _)) (by unfold sourceSamplingCorrelationBudget; positivity)
    (fun n hn k hk hne => by rw [hB,hA]; exact sourceSamplingProduct_pair_error stage hs r b a c a' c' n k hn hk hne)
    (fun n hn => by rw [hM,hA]; exact sourceSamplingProduct_mixed_error stage hs r b E G hE hG n hn)
  have hex := sampling_average_square_expansion μ S f g (fun n _ k _ => hpair n k) (fun n _ => hmix n) hg
  rw [← hex] at hc
  have hErr : (∫ p, ((∑ n ∈ S, f n p)/(S.card : ℝ)-g p)^2 ∂μ) =
      ∫ θ, sourceSamplingSquaredError stage r b E G θ ∂sourceAngleLaw :=
    integral_prod _ (sourceSampling_error_joint_integrable stage r b E G hE hG)
  have hDiag : (∑ n ∈ S, ∫ p, f n p*f n p ∂μ)/(S.card : ℝ)^2 =
      ∫ θ, sourceSamplingDiagonalContribution stage r b E G θ ∂sourceAngleLaw := by
    unfold sourceSamplingDiagonalContribution
    rw [integral_div,integral_finsetSum _ (fun n _ =>
      (sourceSamplingProduct_square_integrable stage r b E G hE hG n).integral_prod_left)]
    simp only [hB,pow_two,f,S]
  rw [hErr,hDiag] at hc
  exact hc

end
end FiniteFactor

end OAI
