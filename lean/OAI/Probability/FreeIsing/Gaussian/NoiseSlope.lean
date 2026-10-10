import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_tendsto_zero_of_tail_tsum_ne_top (X : ℕ → Ω → ℝ)
    (hX : ∀ ε : ℝ, 0 < ε → (∑' n, μ {ω | ε ≤ |X n ω|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  have hsmall : ∀ k : ℕ, ∀ᵐ ω ∂μ,
      ∀ᶠ n in atTop, |X n ω| < 1 / (k + 1 : ℝ) := by
    intro k
    have h := ae_eventually_notMem (hX (1 / (k + 1 : ℝ)) (by positivity))
    simpa only [Set.mem_ofPred_eq, not_le] using h
  filter_upwards [ae_all_iff.mpr hsmall] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hω k)
  exact ⟨N, fun n hn => by simpa [Real.dist_eq] using (hN n hn).trans hk⟩

theorem ae_tendsto_zero_of_summable_tail [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ ε : ℝ, 0 < ε → Summable (fun n => μ.real {ω | ε ≤ |X n ω|})) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_tail_tsum_ne_top X
  intro ε hε
  have h := (hX ε hε).tsum_ofReal_ne_top
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

theorem ae_tendsto_zero_of_exp_tail [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ ε : ℝ, 0 < ε → ∃ C c : ℝ, 0 < c ∧
      ∀ n, μ.real {ω | ε ≤ |X n ω|} ≤ C * Real.exp (-(n : ℝ) * c)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_summable_tail X
  intro ε hε
  obtain ⟨C, c, hc, hbound⟩ := hX ε hε
  have hsum : Summable (fun n : ℕ => C * Real.exp (-(n : ℝ) * c)) := by
    simpa only [mul_neg, neg_mul] using
      (Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hc)).mul_left C
  exact hsum.of_nonneg_of_le (fun _ => measureReal_nonneg) hbound

theorem ae_all_tendsto_zero_of_exp_tail {ι : Type*} [Countable ι] [IsFiniteMeasure μ]
    (X : ι → ℕ → Ω → ℝ)
    (hX : ∀ i ε, 0 < ε → ∃ C c : ℝ, 0 < c ∧
      ∀ n, μ.real {ω | ε ≤ |X i n ω|} ≤ C * Real.exp (-(n : ℝ) * c)) :
    ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n => X i n ω) atTop (𝓝 0) :=
  ae_all_iff.mpr (fun i => ae_tendsto_zero_of_exp_tail (X i) (hX i))

theorem subgaussian_abs_tail [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have hset : {ω | ε ≤ |X ω|} = {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    ext ω
    simpa only [Set.mem_ofPred_eq, Set.mem_union] using (le_abs (a := ε) (b := X ω))
  rw [hset]
  calc
    μ.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω}) ≤
        μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ -X ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * c)) + Real.exp (-ε ^ 2 / (2 * c)) :=
      add_le_add (hX.measure_ge_le hε) (hX.neg.measure_ge_le hε)
    _ = 2 * Real.exp (-ε ^ 2 / (2 * c)) := by ring

theorem ae_tendsto_div_succ_zero_of_subgaussian [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX : ∀ n, HasSubgaussianMGF (X n) ((n : ℝ≥0) + 1) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_exp_tail
  intro ε hε
  refine ⟨2, ε ^ 2 / 2, by positivity, ?_⟩
  intro n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hset : {ω | ε ≤ |X n ω / ((n : ℝ) + 1)|} =
      {ω | ε * ((n : ℝ) + 1) ≤ |X n ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hn, le_div_iff₀ hn]
  rw [hset]
  have ht := subgaussian_abs_tail (hX n) (mul_nonneg hε.le hn.le)
  simp only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] at ht
  refine ht.trans ?_
  have heq : -(ε * ((n : ℝ) + 1)) ^ 2 / (2 * ((n : ℝ) + 1)) =
      -((n : ℝ) + 1) * (ε ^ 2 / 2) := by
    field_simp [ne_of_gt hn]
  rw [heq]
  gcongr
  nlinarith [sq_nonneg ε]

theorem hasSubgaussianMGF_of_hasLaw_gaussian {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ := by
  have hg : HasSubgaussianMGF id v (gaussianReal 0 v) := by
    constructor
    · intro t
      exact integrable_exp_mul_gaussianReal t
    · intro t
      simp [mgf_id_gaussianReal]
  rw [← hX.map_eq] at hg
  simpa only [Function.id_comp] using hg.of_map hX.aemeasurable

theorem ae_brownian_div_succ_tendsto_zero (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => B ((n : ℝ≥0) + 1) ω / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact ae_tendsto_div_succ_zero_of_subgaussian
    (fun n => B ((n : ℝ≥0) + 1))
    (fun n => hasSubgaussianMGF_of_hasLaw_gaussian (hB.hasLaw_eval _))

theorem ae_brownian_div_nat_tendsto_zero (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => B n ω / (n : ℝ)) atTop (𝓝 0) := by
  filter_upwards [ae_brownian_div_succ_tendsto_zero B hB] with ω hω
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hω

theorem ae_all_brownian_div_nat_tendsto_zero {ι : Type*} [Countable ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) μ) :
    ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n : ℕ => B i n ω / (n : ℝ)) atTop (𝓝 0) :=
  ae_all_iff.mpr (fun i => ae_brownian_div_nat_tendsto_zero (B i) (hB i))

theorem ae_brownian_signal_recovery (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B μ) (signal : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => ((n : ℝ) * signal ω + B n ω) / (n : ℝ))
      atTop (𝓝 (signal ω)) := by
  filter_upwards [ae_brownian_div_nat_tendsto_zero B hB] with ω hω
  have ht : Tendsto (fun n : ℕ => signal ω + B n ω / (n : ℝ))
      atTop (𝓝 (signal ω)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hω
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

end Problem367

end OAI
