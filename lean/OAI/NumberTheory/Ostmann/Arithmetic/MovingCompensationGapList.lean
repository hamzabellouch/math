import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationGeometry

namespace OAI

/-! # The prescribed normalized gaps in the backwards target recursion -/

namespace Ostmann
open Filter

noncomputable def movingCompensationGaps (k : ℕ) (BD Bz L : ℝ) : List ℝ :=
  List.ofFn (fun i : Fin k =>
    spectatorStepGap BD Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ (i : ℕ)) (spectatorBulkCount k L) /
      (2 : ℝ) ^ (i : ℕ))

noncomputable def movingCompensationGapRate (k : ℕ) (BD Bz : ℝ) : ℝ :=
  (BD + Bz * Real.log ((k : ℝ) ^ 4) + (2 / 5 : ℝ) * k * Real.log 2) * (k : ℝ) ^ 4

@[simp] theorem movingCompensationGaps_length (k : ℕ) (BD Bz L : ℝ) :
    (movingCompensationGaps k BD Bz L).length = k := by simp [movingCompensationGaps]

theorem movingCompensationGapRate_nonneg (k : ℕ) (hk : 0 < k)
    (BD Bz : ℝ) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    0 ≤ movingCompensationGapRate k BD Bz := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ hk1
  have hzlog := Real.log_nonneg hz
  have h2log : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold movingCompensationGapRate
  positivity

theorem movingCompensationGaps_bounds (k : ℕ) (hk : 0 < k)
    (BD Bz L : ℝ) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hL : 0 ≤ L) :
    ∀ d ∈ movingCompensationGaps k BD Bz L,
      0 ≤ d ∧ d ≤ movingCompensationGapRate k BD Bz * L := by
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
  have hr : (0 : ℝ) < 2 ^ (i : ℕ) := by positivity
  have heq : spectatorStepGap BD Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ (i : ℕ))
      (spectatorBulkCount k L) / (2 : ℝ) ^ (i : ℕ) =
      (BD + Bz * Real.log ((k : ℝ) ^ 4) +
        (2 / 5 : ℝ) * (i : ℕ) * Real.log 2) * (spectatorBulkCount k L : ℝ) := by
    unfold spectatorStepGap
    simp only [Real.log_pow]
    field_simp [hr.ne']
  rw [heq]
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hk)
  have hzlog := Real.log_nonneg hz
  have h2log : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hi : ((i : ℕ) : ℝ) ≤ k := by exact_mod_cast i.isLt.le
  have hc : 0 ≤ BD + Bz * Real.log ((k : ℝ) ^ 4) + (2 / 5 : ℝ) * (i : ℕ) * Real.log 2 := by positivity
  have hc' : BD + Bz * Real.log ((k : ℝ) ^ 4) + (2 / 5 : ℝ) * (i : ℕ) * Real.log 2 ≤
      BD + Bz * Real.log ((k : ℝ) ^ 4) + (2 / 5 : ℝ) * k * Real.log 2 := by
    nlinarith only [hi, h2log]
  refine ⟨mul_nonneg hc (Nat.cast_nonneg _), ?_⟩
  have h1 := mul_le_mul_of_nonneg_right hc' (Nat.cast_nonneg (spectatorBulkCount k L) (α := ℝ))
  have h2 := mul_le_mul_of_nonneg_left (spectatorBulkCount_upper k L hL)
    (hc.trans hc')
  dsimp [movingCompensationGapRate]
  nlinarith only [h1, h2]

theorem eventual_prescribed_compensation_range (k : ℕ) (hk : 0 < k)
    (BD Bz : ℝ) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) :
    ∀ᶠ L : ℝ in atTop, ∀ J : ℝ,
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) →
      ∀ w ∈ movingCompensationTargets J (movingCompensationGaps k BD Bz L),
        Real.exp ((1 / 100 : ℝ) * L) ≤ w / 4 ∧
        w / 4 ≤ Real.exp ((105 / 10000 : ℝ) * L) := by
  filter_upwards [eventual_moving_compensation_range k (movingCompensationGapRate k BD Bz)
      (movingCompensationGapRate_nonneg k hk BD Bz hBD hBz),
    eventually_ge_atTop (0 : ℝ)] with L htarget hL
  intro J hJlo hJhi
  exact htarget J (movingCompensationGaps k BD Bz L)
    (by simp) hJlo hJhi (movingCompensationGaps_bounds k hk BD Bz L hBD hBz hL)

end Ostmann

end OAI
