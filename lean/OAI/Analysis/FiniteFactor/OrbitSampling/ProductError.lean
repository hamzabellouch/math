import OAI.Analysis.FiniteFactor.OrbitSampling.CrossProducts
import OAI.Analysis.FiniteFactor.Sampling.ProductError

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

def sourceSamplingCorrelationBudget (stage : ℕ) : ℝ :=
  ((sourceSamplingPrefix stage).card : ℝ)*(104*(sourceBlockSize stage : ℝ)^(-74 : ℝ))*Real.exp 135

/-- Uniform telescoping budget from the actual ideal coordinate moments. -/
theorem sourceSampling_coordinate_product_error (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (f : SourceCoordinate → ℝ) (hf : ∀ i ∈ sourceSamplingPrefix stage, 0 ≤ f i)
    (he : ∀ i ∈ sourceSamplingPrefix stage,
      |f i-(∫ s, samplingOrientedDensity r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (E i) (G i) s^2 ∂unitIntervalMeasure)| ≤ 104*(sourceBlockSize stage : ℝ)^(-74 : ℝ)) :
    |(∏ i ∈ sourceSamplingPrefix stage, f i)-
      (∫ x, sourceSamplingIdealDensity stage r b E G x^2
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))| ≤ sourceSamplingCorrelationBudget stage := by
  let A (i : SourceCoordinate) := ∫ s, samplingOrientedDensity r (b i) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (E i) (G i) s^2 ∂unitIntervalMeasure
  let x := (sourceBlockSize stage : ℝ)^(-6/5 : ℝ)
  let ε := 104*(sourceBlockSize stage : ℝ)^(-74 : ℝ)
  let M := 1+108*x
  have hm1 : (1 : ℝ) ≤ sourceBlockSize stage := by
    have h : 100 ≤ sourceBlockSize stage := (sourceStage stage).m_ge_100
    exact_mod_cast (show 1 ≤ sourceBlockSize stage by omega)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hεx : ε ≤ 104*x := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num : (-74 : ℝ) ≤ -6/5)) (by norm_num)
  have hA (i : SourceCoordinate) : 0 ≤ A i ∧ A i ≤ 1+4*x :=
    ⟨integral_nonneg (fun _ => sq_nonneg _),(sourceSampling_oriented_moment stage r (b i) (E i) (G i) (hE i) (hG i)).2⟩
  have hfb (i : SourceCoordinate) (hi : i ∈ sourceSamplingPrefix stage) : 0 ≤ f i ∧ f i ≤ M := by
    refine ⟨hf i hi,?_⟩
    have hh := (abs_le.mp (he i hi)).2
    have ha := (hA i).2
    dsimp [M]
    change f i-A i ≤ ε at hh
    linarith
  have hAb (i : SourceCoordinate) (_hi : i ∈ sourceSamplingPrefix stage) : 0 ≤ A i ∧ A i ≤ M :=
    ⟨(hA i).1,(hA i).2.trans (by dsimp [M]; linarith)⟩
  have hpow : M^(sourceSamplingPrefix stage).card ≤ Real.exp 135 := by
    have hp := product_energy_le_exp (fun _i : sourceSamplingPrefix stage => M)
      (fun _i : sourceSamplingPrefix stage => 108*x)
      (fun _ => by dsimp [M]; positivity) (fun _ => le_rfl)
    have hbudget : ((sourceSamplingPrefix stage).card : ℝ)*(108*x) ≤ 135 := by
      have hh := sourceSampling_prefix_quadratic_budget stage
      change ((sourceSamplingPrefix stage).card : ℝ)*(4*x) ≤ 5 at hh
      nlinarith
    have hp' : M^(sourceSamplingPrefix stage).card ≤
        Real.exp (((sourceSamplingPrefix stage).card : ℝ)*(108*x)) := by simpa using hp
    exact hp'.trans (Real.exp_le_exp.mpr hbudget)
  rw [sourceSamplingIdealDensity_square stage r b E G hE hG]
  apply (sampling_product_error (sourceSamplingPrefix stage) f A M ε (by dsimp [M]; linarith) hε hfb hAb he).trans
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Distinct products under the actual angle and Haar laws. -/
theorem sourceSamplingProduct_pair_error (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (r : Bool) (b : SourceCoordinate → Bool) (a c a' c' : SourceCoordinate → ℝ)
    (n k : ℤ) (hn : n ∈ sourceSamplingPowers stage) (hk : k ∈ sourceSamplingPowers stage) (hne : n ≠ k) :
    |(∫ θ, ∫ x, sourceSamplingProduct stage r b (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) n θ x *
        sourceSamplingProduct stage r b (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) k θ x
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) ∂sourceAngleLaw)-
      (∫ x, sourceSamplingIdealDensity stage r b (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) x^2
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))| ≤ sourceSamplingCorrelationBudget stage := by
  rw [integral_integral_swap (sourceSamplingProduct_pair_integrable stage r b _ _
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc) n k),
    sourceSamplingProduct_inner_factorization stage r b _ _ (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc) n k]
  apply sourceSampling_coordinate_product_error stage r b _ _ (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)
  · intro i _
    have hp := sourceSampling_parameters stage
    exact integral_nonneg (fun s => integral_nonneg (fun θ => mul_nonneg
      (samplingOrientedWeight_bounds r (b i) _ _ _ _ hp.1 hp.2.2 s _).1
      (samplingOrientedWeight_bounds r (b i) _ _ _ _ hp.1 hp.2.2 s _).1))
  · intro i hi
    have hip : i.1 ≤ stage := by
      have hh := (CouplingParameters.mem_blockPrefix sourceBlockSize (stage+1) i).mp hi
      omega
    exact sourceSampling_coordinate_pair_error stage hs i hip n k hn hk hne r (b i) (a i) (c i) (a' i) (c' i)

/-- Actual mixed products have the same uniform error budget. -/
theorem sourceSamplingProduct_mixed_error (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (r : Bool) (b : SourceCoordinate → Bool) (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (n : ℤ) (hn : n ∈ sourceSamplingPowers stage) :
    |(∫ θ, ∫ x, sourceSamplingProduct stage r b E G n θ x*sourceSamplingIdealDensity stage r b E G x
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) ∂sourceAngleLaw)-
      (∫ x, sourceSamplingIdealDensity stage r b E G x^2
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))| ≤ sourceSamplingCorrelationBudget stage := by
  rw [integral_integral_swap (sourceSamplingProduct_mixed_integrable stage r b E G hE hG n),
    sourceSamplingProduct_mixed_factorization stage r b E G hE hG n]
  apply sourceSampling_coordinate_product_error stage r b E G hE hG
  · intro i _
    have hp := sourceSampling_parameters stage
    exact integral_nonneg (fun s => mul_nonneg
      (integral_nonneg (fun t => (samplingOrientedWeight_bounds r (b i) _ _ _ _ hp.1 hp.2.2 s t).1))
      (integral_nonneg (fun θ => (samplingOrientedWeight_bounds r (b i) _ _ _ _ hp.1 hp.2.2 s _).1)))
  · intro i hi
    have hip : i.1 ≤ stage := by
      have hh := (CouplingParameters.mem_blockPrefix sourceBlockSize (stage+1) i).mp hi
      omega
    apply (sourceSampling_coordinate_mixed_error stage hs i hip n hn r (b i) (E i) (G i) (hE i) (hG i)).trans
    have hm1 : (1 : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (show 1 ≤ sourceBlockSize stage by omega)
    have he := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num : (-80 : ℝ) ≤ -74)
    nlinarith [Real.rpow_nonneg (sourceBlockSize_pos stage).le (-74 : ℝ)]

end
end FiniteFactor

end OAI
