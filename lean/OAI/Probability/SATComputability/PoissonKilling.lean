import OAI.Probability.SATComputability.CandidateProcess

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem candidateAlive_nonneg {n : ℕ} (U : Finset (DeletionCandidate n)) :
    0 ≤ candidateAlive U := by unfold candidateAlive; split <;> norm_num

theorem candidateAlive_le_one {n : ℕ} (U : Finset (DeletionCandidate n)) :
    candidateAlive U ≤ 1 := by unfold candidateAlive; split <;> norm_num

theorem candidateStep_alive_le {n : ℕ} [NeZero n] (k : ℕ) :
    candidateStep (n := n) k candidateAlive ≤ candidateAlive := by
  intro U
  by_cases hU : U.Nonempty
  · calc
      _ ≤ (FiniteLaw.uniform : FiniteLaw (Fin k → SignedLiteral n)).expect (fun _ => 1) :=
        FiniteLaw.expect_mono _ (fun _ => candidateAlive_le_one _)
      _ = candidateAlive U := by simp [candidateAlive, hU]
  · have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    simp [he, candidateStep, candidateAlive]

theorem batchKillProbability_mono {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) : Monotone (batchKillProbability U k) := by
  have hstep (d : ℕ) : (candidateStep k)^[d+1] candidateAlive ≤
      (candidateStep (n := n) k)^[d] candidateAlive := by
    rw [Function.iterate_succ_apply]
    exact (candidateStep_mono k).iterate d (candidateStep_alive_le k)
  have ha : Antitone (fun d => (candidateStep k)^[d] candidateAlive U) :=
    antitone_nat_of_succ_le (fun d => hstep d U)
  intro d e hde
  rw [candidateKill_iterate, candidateKill_iterate]
  linarith [ha hde]

theorem batchKillProbability_nonneg {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) : 0 ≤ batchKillProbability U k d := by
  apply FiniteLaw.expect_nonneg
  intro cs
  split <;> norm_num

theorem batchKillProbability_le_one {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) : batchKillProbability U k d ≤ 1 := by
  apply (FiniteLaw.expect_mono _ (g := fun _ => 1) ?_).trans_eq (FiniteLaw.expect_const _ _)
  intro cs
  split <;> norm_num

theorem poisson_power_integrable (r : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun m : ℕ => x^m) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have h := ((NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*x)).mul_left
    (Real.exp (-(r : ℝ)))).summable
  convert h using 1
  funext m
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx m), mul_pow]
  ring

theorem poisson_power_integral (r : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    (∫ m : ℕ, x^m ∂poissonMeasure r) = Real.exp ((r : ℝ)*(x-1)) := by
  rw [integral_poissonMeasure' (poisson_power_integrable r hx)]
  have h := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*x)).mul_left
    (Real.exp (-(r : ℝ)))
  calc
    _ = ∑' m : ℕ, Real.exp (-(r : ℝ)) * (((r : ℝ)*x)^m / m.factorial) := by
      apply tsum_congr
      intro m
      simp only [smul_eq_mul, mul_pow]
      ring
    _ = Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ)*x) := by
      simpa only [← Real.exp_eq_exp_ℝ] using h.tsum_eq
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem poisson_tail_dyadic (r : ℝ≥0) (L : ℕ) :
    (∫ m : ℕ, if L < m then (1 : ℝ) else 0 ∂poissonMeasure r) ≤
      Real.exp r / (2 : ℝ)^L := by
  have hi : Integrable (fun m : ℕ => if L < m then (1 : ℝ) else 0)
      (poissonMeasure r) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun m => by split <;> norm_num)
  calc
    _ ≤ ∫ m : ℕ, (2 : ℝ)^m / (2 : ℝ)^L ∂poissonMeasure r := by
      apply integral_mono hi ((poisson_power_integrable r (by norm_num : (0 : ℝ) ≤ 2)).div_const _)
      intro m
      dsimp only
      split_ifs with hm
      · apply (le_div_iff₀ (by positivity)).mpr
        simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm.le)
      · positivity
    _ = _ := by rw [integral_div, poisson_power_integral r (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

noncomputable def poissonKillProbability {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) (r : ℝ≥0) : ℝ :=
  ∫ d : ℕ, batchKillProbability U k d ∂poissonMeasure r

theorem poissonKillProbability_truncate {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k L : ℕ) (r : ℝ≥0) :
    poissonKillProbability U k r ≤ batchKillProbability U k L +
      Real.exp r / (2 : ℝ)^L := by
  have hi : Integrable (fun d => batchKillProbability U k d) (poissonMeasure r) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun d => (abs_le.mpr
      ⟨by linarith [batchKillProbability_nonneg U k d], batchKillProbability_le_one U k d⟩))
  have ht : Integrable (fun d : ℕ => if L < d then (1 : ℝ) else 0)
      (poissonMeasure r) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun d => by split <;> norm_num)
  unfold poissonKillProbability
  calc
    _ ≤ ∫ d : ℕ, batchKillProbability U k L +
        (if L < d then (1 : ℝ) else 0) ∂poissonMeasure r := by
      apply integral_mono hi ((integrable_const _).add ht)
      intro d
      dsimp only [Pi.add_apply]
      split_ifs with hd
      · linarith [batchKillProbability_le_one U k d, batchKillProbability_nonneg U k L]
      · simpa using batchKillProbability_mono U k (Nat.le_of_not_gt hd)
    _ = batchKillProbability U k L +
        (∫ d : ℕ, if L < d then (1 : ℝ) else 0 ∂poissonMeasure r) := by
      rw [integral_add (integrable_const _) ht, integral_const, probReal_univ, one_smul]
    _ ≤ _ := add_le_add le_rfl (poisson_tail_dyadic r L)

theorem poissonKillProbability_mono_rate {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) :
    Monotone (poissonKillProbability U k) := by
  have hi (r : ℝ≥0) : Integrable (fun d => batchKillProbability U k d)
      (poissonMeasure r) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun d => abs_le.mpr
      ⟨by linarith [batchKillProbability_nonneg U k d], batchKillProbability_le_one U k d⟩)
  intro r s hrs
  have hs : s = r + (s-r) := (add_tsub_cancel_of_le hrs).symm
  unfold poissonKillProbability
  rw [hs, ← poissonMeasure_conv_poissonMeasure, integral_conv (by
    simpa only [poissonMeasure_conv_poissonMeasure] using hi (r+(s-r)))]
  apply integral_mono (hi r)
  · apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Eventually.of_forall (fun d => by
      simpa only [Real.norm_eq_abs] using
        (abs_integral_le_bound (μ := poissonMeasure (s-r)) (fun e => abs_le.mpr
          ⟨by linarith [batchKillProbability_nonneg U k (d+e)],
            batchKillProbability_le_one U k (d+e)⟩)))
  · intro d
    have hshift : Integrable (fun e => batchKillProbability U k (d+e))
        (poissonMeasure (s-r)) := by
      apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      exact Eventually.of_forall (fun e => abs_le.mpr
        ⟨by linarith [batchKillProbability_nonneg U k (d+e)], batchKillProbability_le_one U k (d+e)⟩)
    calc
      _ = ∫ _e : ℕ, batchKillProbability U k d ∂poissonMeasure (s-r) := by simp
      _ ≤ _ := integral_mono (integrable_const _) hshift
        (fun e => batchKillProbability_mono U k (Nat.le_add_right d e))

end FixedClauseThreshold.Computability

end OAI
