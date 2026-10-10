import OAI.Probability.SATComputability.MeanSurvival

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Classical NNReal

theorem candidateStep_minimumDeletions_le {n : ℕ} [NeZero n] (m : ℕ) :
    (candidateStep (n := n) 3)^[m] (fun U => (minimumDeletions U : ℝ)) Finset.univ ≤
      relaxedFixedMinimum n m := by
  rw [candidateStep_iterate, finite_uniform_expect_eq_mean]
  let e := Equiv.piCongrRight (fun _ : Fin m => relaxedClauseEquiv n)
  rw [← uniformMean_equiv e]
  apply uniformMean_mono
  intro cs
  exact_mod_cast candidate_minimumDeletions_le cs

theorem candidateBlock_minimumDeletions_le (n : ℕ) [NeZero n] (a : ℝ≥0) :
    (candidateBlock (n := n) (a*n) 3 Finset.univ).expect
      (fun U => (minimumDeletions U : ℝ)) ≤ relaxedPoissonMinimum n a := by
  rw [candidateBlock_expect, relaxedPoissonMinimum]
  apply integral_mono
  · simpa only [candidateFixedBlock_expect] using
      poissonMixture_integrable_expect (a*n)
        (fun m => candidateFixedBlock (n := n) 3 m Finset.univ)
        (fun U => (minimumDeletions U : ℝ))
  · apply (poisson_integrable_count (a*n)).mono'
      (measurable_of_countable _).aestronglyMeasurable
    exact ae_of_all _ (fun m => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (relaxedFixedMinimum_nonneg n m)] using
        relaxedFixedMinimum_le n m)
  · exact candidateStep_minimumDeletions_le

theorem mean_lifetime_energy_lower {n r t : ℕ} [NeZero n]
    (hr : r ≤ n+1) (ht : 0 < t) (htM : t ≤ 20*n) (a : ℝ≥0)
    (hta : (t : ℝ≥0) ≤ a*n) :
    (r : ℝ)*(1-
      (FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)).expect
        (maskLifetime (20*n) (deletionBudgetMask n r)) / t) ≤
      relaxedPoissonMinimum n a := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hs := survival_le_mean_lifetime htM (deletionBudgetMask n r)
  have hp := candidateBlock_survival_antitone 3 (deletionBudgetMask n r) hta
  have hq : (candidateBlock (n := n) t 3 (deletionBudgetMask n r)).expect candidateAlive ≤
      (FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)).expect
        (maskLifetime (20*n) (deletionBudgetMask n r)) / t :=
    (le_div_iff₀ htR).mpr (by nlinarith only [hs])
  have hb := block_minimumDeletions_lower hr (a*n)
  have hm := candidateBlock_minimumDeletions_le n a
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left (hp.trans hq) 1)
    (Nat.cast_nonneg r)).trans (hb.trans hm)

end FixedClauseThreshold.Computability

end OAI
