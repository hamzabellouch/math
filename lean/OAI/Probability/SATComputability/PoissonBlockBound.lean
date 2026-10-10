import OAI.Probability.SATComputability.PoissonKernel

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory ProbabilityTheory Filter
open scoped NNReal

theorem poisson_count_lower_half {M : ℕ} (hM : 0 < M) (μ : ℝ≥0)
    (hμ : 4 * (M : ℝ) ≤ μ) :
    (1 : ℝ)/2 ≤ ∫ m : ℕ, if M ≤ m then (1 : ℝ) else 0 ∂poissonMeasure μ := by
  have hMn : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hden : 0 < (μ : ℝ) - M := by linarith
  have hint : Integrable (fun m : ℕ => if m < M then (1 : ℝ) else 0)
      (poissonMeasure μ) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun m => by split <;> norm_num)
  have hvar : Integrable (fun m : ℕ => ((m : ℝ)-(μ : ℝ))^2) (poissonMeasure μ) := by
    convert ((poisson_integrable_count_sq μ).sub
      ((poisson_integrable_count μ).const_mul (2*(μ : ℝ)))).add
      (integrable_const ((μ : ℝ)^2)) using 1
    funext m
    dsimp only [Pi.add_apply, Pi.sub_apply]
    ring
  have htail : (∫ m : ℕ, if m < M then (1 : ℝ) else 0 ∂poissonMeasure μ) ≤
      (μ : ℝ) / ((μ : ℝ)-M)^2 := by
    calc
      _ ≤ ∫ m : ℕ, ((m : ℝ)-(μ : ℝ))^2 / ((μ : ℝ)-M)^2 ∂poissonMeasure μ := by
        apply integral_mono hint (hvar.div_const _)
        intro m
        dsimp only
        split_ifs with hm
        · have hm' : (m : ℝ) < M := by exact_mod_cast hm
          apply (le_div_iff₀ (sq_pos_of_pos hden)).mpr
          nlinarith [sq_nonneg ((m : ℝ)-(μ : ℝ))]
        · positivity
      _ = _ := by rw [integral_div, poisson_variance]
  have hnum : (μ : ℝ) / ((μ : ℝ)-M)^2 ≤ (1 : ℝ)/2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    have hfour : (4 : ℝ) ≤ μ := by linarith
    have hproduct := mul_nonneg (show (0 : ℝ) ≤ μ-4*M by linarith)
      (show (0 : ℝ) ≤ μ+2*M-2 by linarith)
    have hMproduct := mul_nonneg (show (0 : ℝ) ≤ M-1 by linarith)
      (show (0 : ℝ) ≤ 9*M by positivity)
    nlinarith
  have he : (∫ m : ℕ, if M ≤ m then (1 : ℝ) else 0 ∂poissonMeasure μ) =
      1 - ∫ m : ℕ, if m < M then (1 : ℝ) else 0 ∂poissonMeasure μ := by
    have hp (m : ℕ) : (if M ≤ m then (1 : ℝ) else 0) =
        1 - (if m < M then (1 : ℝ) else 0) := by
      by_cases h : M ≤ m <;> simp [h, Nat.not_lt.mpr, Nat.lt_of_not_ge]
    simp_rw [hp]
    rw [integral_sub (integrable_const 1) hint]
    simp
  rw [he]
  linarith

theorem poisson_block_kill_lower {n M : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) (hM : 0 < M) (μ : ℝ≥0)
    (hμ : 4 * (M : ℝ) ≤ μ) :
    batchKillProbability U k M / 2 ≤ poissonKillProbability U k μ := by
  have hi : Integrable (fun m => batchKillProbability U k m) (poissonMeasure μ) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun m => abs_le.mpr
      ⟨by linarith [batchKillProbability_nonneg U k m], batchKillProbability_le_one U k m⟩)
  have hj : Integrable (fun m : ℕ => if M ≤ m then (1 : ℝ) else 0)
      (poissonMeasure μ) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun m => by split <;> norm_num)
  have h := integral_mono (hj.const_mul (batchKillProbability U k M)) hi (fun m => by
    dsimp only
    split_ifs with hm
    · simpa using batchKillProbability_mono U k hm
    · simpa using batchKillProbability_nonneg U k m)
  rw [integral_const_mul] at h
  have hl := mul_le_mul_of_nonneg_left (poisson_count_lower_half hM μ hμ)
    (batchKillProbability_nonneg U k M)
  unfold poissonKillProbability
  linarith

theorem poisson_two_to_three_block {n L d : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (hd : 0 < d) (hL : 0 < L)
    {q : ℝ} (hq : q ≤ poissonKillProbability U 2 60)
    (htail : Real.exp 60 / (2 : ℝ)^L ≤ q/4)
    (hrepl : (L : ℝ)/(d : ℝ)^2 ≤ q/4)
    (μ : ℝ≥0) (hμ : 4 * (L*d : ℕ) ≤ (μ : ℝ)) :
    q/4 ≤ poissonKillProbability U 3 μ := by
  have ht := poissonKillProbability_truncate U 2 L 60
  have hr := relaxed_sequential_replacement U hd L
  have hb := poisson_block_kill_lower U 3 (Nat.mul_pos hL hd) μ hμ
  norm_num only [NNReal.coe_ofNat] at ht
  linarith

end FixedClauseThreshold.Computability

end OAI
