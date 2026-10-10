import OAI.NumberTheory.Ostmann.Arithmetic.MovingProtectedTarget

namespace OAI

/-! # The backwards target construction preserves the original total log size -/

namespace Ostmann
open scoped BigOperators

theorem movingCompensationTargetError_ofFn (k : ℕ) (d : Fin k → ℝ) :
    movingCompensationTargetError (List.ofFn d) = ∑ i : Fin k, (2 : ℝ) ^ (i : ℕ) * d i := by
  induction k with
  | zero => simp [movingCompensationTargetError]
  | succ k ih =>
    rw [List.ofFn_succ, movingCompensationTargetError, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
    calc
      _ = d 0 + ∑ i : Fin k, 2 * (2 ^ (i : ℕ) * d i.succ) := by
        rw [← Finset.mul_sum]
        ring
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring

theorem movingCompensationTargetError_gaps (k : ℕ) (BD Bz L : ℝ) :
    movingCompensationTargetError (movingCompensationGaps k BD Bz L) =
      ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ (i : ℕ))
        (spectatorBulkCount k L) := by
  unfold movingCompensationGaps
  rw [movingCompensationTargetError_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  have hr : (2 : ℝ) ^ (i : ℕ) ≠ 0 := by positivity
  field_simp

theorem moving_protected_and_compensation_total (k : ℕ) (BD Bz L logX G td Δ₀ : ℝ) :
    let gaps := movingCompensationGaps k BD Bz L
    let J := movingProtectedTarget k logX G td
      (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
        ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L))
    2 * G + 2 * td + J + (movingCompensationTargets J gaps).sum = logX + Δ₀ := by
  intro gaps J
  have hs := movingCompensationTargets_sum J gaps
  have hlen : gaps.length = k := movingCompensationGaps_length k BD Bz L
  rw [hlen, movingCompensationTargetError_gaps] at hs
  have hJ : (2 : ℝ) ^ k * J = logX - 2 * G - 2 * td +
      (Δ₀ + ∑ i : Fin k, spectatorStepGap BD Bz ((k : ℝ) ^ 4)
        ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L)) := by
    dsimp [J, movingProtectedTarget]
    field_simp
  linarith

end Ostmann

end OAI
