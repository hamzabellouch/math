import Mathlib

namespace OAI

/-!
# Summability of the exact-correction scales

The iteration uses `t ↦ t^(6/5)`. For an explicit sufficiently small initial
scale, the entire sequence is dominated by a geometric series. This gives
the displacement budget needed for the exact correction.
-/

namespace ClosedSurfaceR4.ExactCorrection

open Filter
open scoped Topology

/-- The fast-decaying scale used in successive smoothing steps. -/
noncomputable def correctionScale (t : ℝ) : ℕ → ℝ
  | 0 => t
  | n + 1 => (correctionScale t n) ^ (6 / 5 : ℝ)

lemma correctionScale_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ correctionScale t n := by
  induction n with
  | zero => exact ht
  | succ n hn => exact Real.rpow_nonneg hn _

lemma scale_step_le_half {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1 / 32) :
    t ^ (6 / 5 : ℝ) ≤ t / 2 := by
  have hfifth : t ^ (1 / 5 : ℝ) ≤ 1 / 2 := by
    calc
      _ ≤ ((1 / 2 : ℝ) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) := by
        apply Real.rpow_le_rpow ht _ (by norm_num)
        norm_num at hsmall ⊢
        exact hsmall
      _ = 1 / 2 := by
        rw [← Real.rpow_natCast_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
        norm_num
  by_cases hzero : t = 0
  · subst t
    norm_num
  · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    rw [show (6 / 5 : ℝ) = 1 + 1 / 5 by norm_num, Real.rpow_add hpos,
      Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hfifth ht]

/-- A concrete geometric majorant, independent of the later block lengths. -/
theorem correctionScale_le_geometric {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1 / 32)
    (n : ℕ) : correctionScale t n ≤ t * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp [correctionScale]
  | succ n hn =>
    have hhalf : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hnt : correctionScale t n ≤ t := hn.trans (by nlinarith)
    have hstep := scale_step_le_half (correctionScale_nonneg ht n) (hnt.trans hsmall)
    change (correctionScale t n) ^ (6 / 5 : ℝ) ≤ _
    calc
      _ ≤ correctionScale t n / 2 := hstep
      _ ≤ (t * (1 / 2 : ℝ) ^ n) / 2 := by linarith
      _ = t * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

/-- The exact-correction scales have total mass strictly less than `1/4`. -/
theorem correctionScale_summable {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1 / 32) :
    Summable (correctionScale t) ∧ (∑' n, correctionScale t n) < 1 / 4 := by
  have hgeom : Summable (fun n : ℕ => t * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left t
  have hs : Summable (correctionScale t) :=
    Summable.of_nonneg_of_le (correctionScale_nonneg ht)
      (correctionScale_le_geometric ht hsmall) hgeom
  refine ⟨hs, ?_⟩
  have hle := hs.tsum_le_tsum (correctionScale_le_geometric ht hsmall) hgeom
  have hsum : (∑' n : ℕ, t * (1 / 2 : ℝ) ^ n) = 2 * t := by
    rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)]
    ring
  rw [hsum] at hle
  linarith

end ClosedSurfaceR4.ExactCorrection

end OAI
