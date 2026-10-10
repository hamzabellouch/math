import OAI.Combinatorics.EditApproximation.Probability.ExactSampling
import Mathlib.Probability.Distributions.Geometric
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A probability law for terminating fair-word rejection executions.
It records the failed trial count and accepted integer, identifies their
joint masses with literal finite fair-word traces, and charges all trials. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory



theorem rejectionSuccessParameter_ne_zero (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    rejectionSuccessParameter N R hN hNR ≠ 0 := by
  intro h
  have heq := congrArg (fun p : unitInterval => (p : ℝ)) h
  have hpos : (0 : ℝ) < (N : ℝ) / R :=
    div_pos (by exact_mod_cast hN) (by exact_mod_cast hN.trans_le hNR)
  change (N : ℝ) / R = 0 at heq
  linarith

theorem rejectionSuccessParameter_complement (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    1 - (rejectionSuccessParameter N R hN hNR : ℝ) = ((R - N : ℕ) : ℝ) / R := by
  change 1 - (N : ℝ) / R = _
  rw [Nat.cast_sub hNR]
  have hR : (R : ℝ) ≠ 0 := by exact_mod_cast (hN.trans_le hNR).ne'
  field_simp [hR]

noncomputable def rejectionExecutionLaw (N R : ℕ) [NeZero N]
    (hN : 0 < N) (hNR : N ≤ R) : Measure (ℕ × Fin N) :=
  (geometricMeasure (rejectionSuccessParameter N R hN hNR)).prod
    (PMF.uniformOfFintype (Fin N)).toMeasure

instance rejectionExecutionLaw_probability (N R : ℕ) [NeZero N]
    (hN : 0 < N) (hNR : N ≤ R) :
    IsProbabilityMeasure (rejectionExecutionLaw N R hN hNR) := by
  unfold rejectionExecutionLaw
  infer_instance

/-- The accepted value has exactly the uniform law, independently of the
number of failed trials. -/
theorem rejectionExecutionLaw_output (N R : ℕ) [NeZero N]
    (hN : 0 < N) (hNR : N ≤ R) :
    (rejectionExecutionLaw N R hN hNR).map Prod.snd =
      (PMF.uniformOfFintype (Fin N)).toMeasure := by
  simp [rejectionExecutionLaw]

/-- Each execution atom has the probability of the corresponding literal
finite first-success trace event. -/
theorem rejectionExecutionLaw_atom (N R : ℕ) [NeZero N]
    (hN : 0 < N) (hNR : N ≤ R) (failures : ℕ) (accepted : Fin N) :
    (rejectionExecutionLaw N R hN hNR).real {(failures, accepted)} =
      ((R - N : ℕ) : ℝ) ^ failures / ((R : ℝ) ^ failures * R) := by
  have hu : ((PMF.uniformOfFintype (Fin N)).toMeasure).real {accepted} = (1 : ℝ) / N := by
    rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [PMF.uniformOfFintype_apply]
  rw [rejectionExecutionLaw, ← Set.singleton_prod_singleton, measureReal_prod_prod,
    geometricMeasure_real_singleton (rejectionSuccessParameter_ne_zero N R hN hNR), hu,
    rejectionSuccessParameter_complement]
  change ((((R - N : ℕ) : ℝ) / R) ^ failures * ((N : ℝ) / R)) * (1 / N) = _
  rw [div_pow]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem rejectionExecutionLaw_literal_trace (N R : ℕ) [NeZero N]
    (hN : 0 < N) (hNR : N ≤ R) (failures : ℕ) (accepted : Fin N) :
    let : NeZero R := ⟨by omega⟩
    (rejectionExecutionLaw N R hN hNR).real {(failures, accepted)} =
      ((PMF.uniformOfFintype ((Fin failures → Fin R) × Fin R)).toMeasure).real
        (firstSuccessEvent N R failures accepted) := by
  let : NeZero R := ⟨by omega⟩
  dsimp only
  rw [rejectionExecutionLaw_atom, firstSuccessEvent_probability N R failures hN hNR accepted]

theorem rejection_trial_moment (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    (∫ failures : ℕ, ((failures : ℝ) + 1)
      ∂geometricMeasure (rejectionSuccessParameter N R hN hNR)) = (R : ℝ) / N := by
  rw [integral_geometricMeasure (rejectionSuccessParameter_ne_zero N R hN hNR)]
  have hterm (k : ℕ) :
      ((1 - (rejectionSuccessParameter N R hN hNR : ℝ)) ^ k *
          (rejectionSuccessParameter N R hN hNR : ℝ)) * ((k : ℝ) + 1) =
        ((k : ℝ) + 1) * N * (((R - N : ℕ) : ℝ) ^ k / ((R : ℝ) ^ k * R)) := by
    rw [rejectionSuccessParameter_complement]
    change (((R - N : ℕ) : ℝ) / R) ^ k * ((N : ℝ) / R) * ((k : ℝ) + 1) = _
    rw [div_pow]
    ring
  simp_rw [smul_eq_mul, hterm]
  exact (rejection_first_success_expected_trials N R hN hNR).tsum_eq

theorem rejection_trials_integrable (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    Integrable (fun failures : ℕ => (failures : ℝ) + 1)
      (geometricMeasure (rejectionSuccessParameter N R hN hNR)) := by
  apply (integrable_geometricMeasure_iff (rejectionSuccessParameter_ne_zero N R hN hNR)).mpr
  have hterm (k : ℕ) :
      (1 - (rejectionSuccessParameter N R hN hNR : ℝ)) ^ k *
        (rejectionSuccessParameter N R hN hNR : ℝ) * ‖(k : ℝ) + 1‖ =
      ((k : ℝ) + 1) * N * (((R - N : ℕ) : ℝ) ^ k / ((R : ℝ) ^ k * R)) := by
    rw [Real.norm_of_nonneg (by positivity), rejectionSuccessParameter_complement]
    change (((R - N : ℕ) : ℝ) / R) ^ k * ((N : ℝ) / R) * ((k : ℝ) + 1) = _
    rw [div_pow]
    ring
  simpa only [hterm] using (rejection_first_success_expected_trials N R hN hNR).summable

/-- All failed trials are included in this strict factor-two bound. -/
theorem rejection_fair_word_trial_moment (N : ℕ) (hN : 0 < N) :
    (∫ failures : ℕ, ((failures : ℝ) + 1)
      ∂geometricMeasure (rejectionSuccessParameter N (2 ^ rejectionBitCount N)
        hN (rejectionWord_range N hN).1)) < 2 := by
  rw [rejection_trial_moment]
  apply (div_lt_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
  exact_mod_cast (rejectionWord_range N hN).2

/-- Exact expected number of consumed fair bits, including failed words. -/
theorem rejection_consumed_bits_moment (N : ℕ) (hN : 0 < N) :
    (∫ failures : ℕ, (((failures : ℝ) + 1) * rejectionBitCount N)
      ∂geometricMeasure (rejectionSuccessParameter N (2 ^ rejectionBitCount N)
        hN (rejectionWord_range N hN).1)) ≤ 2 * rejectionBitCount N := by
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right
    (rejection_fair_word_trial_moment N hN).le (Nat.cast_nonneg _)


end EditApproximation

end OAI
