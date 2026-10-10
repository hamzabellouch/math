import OAI.Analysis.FiniteFactor.OrbitSampling.Error

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical Topology
noncomputable section

/-- The distinct and mixed error budget is summable along the actual stages. -/
theorem sourceSamplingCorrelationBudget_summable : Summable sourceSamplingCorrelationBudget := by
  apply (sourceSampling_inverse_square_summable.mul_left (208*Real.exp 135)).of_nonneg_of_le
  · intro stage; unfold sourceSamplingCorrelationBudget; positivity
  intro stage
  let m : ℝ := sourceBlockSize stage
  have hm : 0 < m := sourceBlockSize_pos stage
  have hm1 : 1 ≤ m := by
    have hh : 100 ≤ sourceBlockSize stage := (sourceStage stage).m_ge_100
    dsimp [m]
    exact_mod_cast (show 1 ≤ sourceBlockSize stage by omega)
  have hd : ((sourceSamplingPrefix stage).card : ℝ) ≤ 2*m :=
    (sourceSamplingPrefix_card_bound stage).trans (by dsimp [m]; nlinarith)
  have he : m*m^(-74 : ℝ) = m^(-73 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one m]
    rw [← Real.rpow_add hm]; norm_num
  calc
    sourceSamplingCorrelationBudget stage ≤ (2*m)*(104*m^(-74 : ℝ))*Real.exp 135 := by
      unfold sourceSamplingCorrelationBudget
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (by positivity)) (by positivity)
    _ = (208*Real.exp 135)*m^(-73 : ℝ) := by rw [← he]; ring
    _ ≤ (208*Real.exp 135)*m^(-2 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)) (by positivity)

/-- Summable expectations for the full empirical sampling error. -/
theorem sourceSamplingSquaredError_summable_integral (r : Bool) (b : SourceCoordinate → Bool)
    (a c a' c' : SourceCoordinate → ℝ) :
    Summable (fun stage => ∫ θ, sourceSamplingSquaredError stage r b
      (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ ∂sourceAngleLaw) := by
  have hd := sourceSamplingDiagonalContribution_summable_integral r b
    (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i))
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)
  have hb := hd.add (sourceSamplingCorrelationBudget_summable.mul_left 3)
  apply hb.of_norm_bounded_eventually_nat
  filter_upwards [sourceBlockSize_tendsto.eventually (eventually_ge_atTop 200000)] with stage hs
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (sourceSamplingSquaredError_nonneg stage r b _ _))]
  exact sourceSamplingSquaredError_expectation stage hs r b a c a' c'

/-- The full squared sampling error is summable and converges to zero on a
conull set of actual source angles. This is not just the self-pair event. -/
theorem sourceSamplingSquaredError_ae (r : Bool) (b : SourceCoordinate → Bool)
    (a c a' c' : SourceCoordinate → ℝ) :
    ∀ᵐ θ ∂sourceAngleLaw,
      Summable (fun stage => sourceSamplingSquaredError stage r b
        (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ) ∧
      Tendsto (fun stage => sourceSamplingSquaredError stage r b
        (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ) atTop (𝓝 0) := by
  have he := sampling_ae_summable_of_integrals sourceAngleLaw
    (fun stage θ => sourceSamplingSquaredError stage r b (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ)
    (fun stage => sourceSamplingSquaredError_measurable stage r b _ _ (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc))
    (fun stage => sourceSamplingSquaredError_integrable stage r b _ _ (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc))
    (fun stage θ => sourceSamplingSquaredError_nonneg stage r b _ _ θ)
    (sourceSamplingSquaredError_summable_integral r b a c a' c')
  exact he.mono (fun θ hθ => ⟨hθ,hθ.tendsto_atTop_zero⟩)

/-- One source-angle event handles any countable family of interval tests,
orientations and triangular-coordinate choices for the full error. -/
theorem sourceSamplingSquaredError_countable_event {ι : Type*} [Countable ι]
    (r : ι → Bool) (b : ι → SourceCoordinate → Bool)
    (a c a' c' : ι → SourceCoordinate → ℝ) :
    ∀ᵐ θ ∂sourceAngleLaw, ∀ j,
      Summable (fun stage => sourceSamplingSquaredError stage (r j) (b j)
        (fun i => Set.Icc (a j i) (c j i)) (fun i => Set.Icc (a' j i) (c' j i)) θ) ∧
      Tendsto (fun stage => sourceSamplingSquaredError stage (r j) (b j)
        (fun i => Set.Icc (a j i) (c j i)) (fun i => Set.Icc (a' j i) (c' j i)) θ) atTop (𝓝 0) :=
  ae_all_iff.mpr (fun j => sourceSamplingSquaredError_ae (r j) (b j) (a j) (c j) (a' j) (c' j))

end
end FiniteFactor

end OAI
