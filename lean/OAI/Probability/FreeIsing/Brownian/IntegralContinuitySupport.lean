import OAI.Probability.FreeIsing.Brownian.IntegralProcess

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem exists_rapid_meanSquare_subsequence
    {X : ℕ → Ω → ℝ} (hX : ∀ n, MemLp (X n) 2 P)
    (hCauchy : CauchySeq (fun n => (hX n).toLp (X n))) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      Summable (fun n => (4 : ℝ) ^ n *
        ∫ ω, (X (k (n + 1)) ω - X (k n) ω) ^ 2 ∂P) := by
  obtain ⟨k, hk, hstep⟩ := Metric.exists_subseq_bounded_of_cauchySeq
    (fun n => (hX n).toLp (X n)) hCauchy
    (fun n => (1 / 4 : ℝ) ^ n) (fun n => by positivity)
  refine ⟨k, hk, ?_⟩
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (integral_nonneg (fun ω => sq_nonneg _)))
    (f := fun n => (1 / 4 : ℝ) ^ n) ?_
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  intro n
  have hnorm : ‖(hX (k (n + 1))).toLp (X (k (n + 1))) -
      (hX (k n)).toLp (X (k n))‖ ≤ (1 / 4 : ℝ) ^ n := by
    simpa only [dist_eq_norm] using
      (hstep n (k (n + 1)) (hk.monotone (Nat.le_succ n))).le
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (1 / 4 : ℝ) ^ n)).2 hnorm
  rw [BrownianGrid.norm_sq_toLp_sub] at hsq
  calc
    _ ≤ (4 : ℝ) ^ n * ((1 / 4 : ℝ) ^ n) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by
      simp only [pow_two, ← mul_pow]
      norm_num

omit [MeasurableSpace Ω] in
theorem continuous_stoppedUniformSum
    {B H : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hB : Continuous (fun t => B t ω)) (T : ℝ≥0) (n : ℕ) :
    Continuous (fun t => stoppedUniformSum B H T n t ω) := by
  unfold stoppedUniformSum
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul
    ((hB.comp (continuous_id.min continuous_const)).sub
      (hB.comp (continuous_id.min continuous_const)))

theorem ae_continuous_stoppedUniformSum
    {B H : ℝ≥0 → Ω → ℝ}
    (hB : ∀ᵐ ω ∂P, Continuous (fun t => B t ω)) (T : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂P, Continuous (fun t => stoppedUniformSum B H T n t ω) := by
  filter_upwards [hB] with ω hω
  exact continuous_stoppedUniformSum hω T n

omit [MeasurableSpace Ω] in
@[simp] theorem stoppedUniformSum_zero (B H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) :
    stoppedUniformSum B H T n 0 = 0 := by
  funext ω
  simp [stoppedUniformSum, StoppedSimpleIntegral.intervalSum]

theorem initial_zero_of_stopped_uniform_limit
    {B H M : ℝ≥0 → Ω → ℝ} (T : ℝ≥0) (hM : MemLp (M 0) 2 P)
    (hlim : Tendsto (fun n => ∫ ω,
      (stoppedUniformSum B H T n 0 ω - M 0 ω) ^ 2 ∂P) atTop (𝓝 0)) :
    M 0 =ᵐ[P] 0 := by
  have hlim' : Tendsto (fun _ : ℕ => ∫ ω, (M 0 ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simpa only [stoppedUniformSum_zero, Pi.zero_apply, zero_sub, neg_sq] using hlim
  have hzero : (∫ ω, (M 0 ω) ^ 2 ∂P) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hlim'
  apply ae_eq_of_integral_sq_sub_eq_zero
  · simpa only [Pi.zero_apply, sub_zero] using hM.integrable_sq
  · simpa only [Pi.zero_apply, sub_zero] using hzero

end Problem367.BrownianIntegralProcess

end

end OAI
