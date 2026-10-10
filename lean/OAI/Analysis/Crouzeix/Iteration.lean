import Mathlib
import OAI.Analysis.Crouzeix.SteinMetric

namespace OAI

/-! Iteration. -/

noncomputable section

open Filter

open scoped Topology

namespace CrouzeixHilbert.Realization

section Iteration

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
lemma norm_pow_contraction (a : A) (ha : ‖a‖ ≤ 1) (j : ℕ) : ‖a ^ j‖ ≤ 1 := by
  exact (norm_pow_le a j).trans (by simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg a) ha j)

theorem summable_two_sided_series (D C a : A) (hD : spectralRadius ℂ D < 1)
    (ha : ‖a‖ ≤ 1) : Summable (fun j : ℕ => D ^ j * C * a ^ j) := by
  apply ((Metric.summable_norm_pow D hD).mul_right ‖C‖).of_norm_bounded
  intro j
  calc
    ‖D ^ j * C * a ^ j‖ ≤ ‖D ^ j * C‖ * ‖a ^ j‖ := norm_mul_le _ _
    _ ≤ ‖D ^ j * C‖ * 1 := mul_le_mul_of_nonneg_left (norm_pow_contraction a ha j) (norm_nonneg _)
    _ ≤ ‖D ^ j‖ * ‖C‖ := by simpa only [mul_one] using norm_mul_le (D ^ j) C

theorem tendsto_two_sided_remainder (D L a : A) (hD : spectralRadius ℂ D < 1)
    (ha : ‖a‖ ≤ 1) : Tendsto (fun j : ℕ => D ^ j * L * a ^ j) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) ?_ ?_ (g := fun j => ‖D ^ j‖ * ‖L‖)
  · intro j
    calc
      ‖D ^ j * L * a ^ j‖ ≤ ‖D ^ j * L‖ * ‖a ^ j‖ := norm_mul_le _ _
      _ ≤ ‖D ^ j * L‖ * 1 := mul_le_mul_of_nonneg_left (norm_pow_contraction a ha j) (norm_nonneg _)
      _ ≤ ‖D ^ j‖ * ‖L‖ := by simpa only [mul_one] using norm_mul_le (D ^ j) L
  · simpa only [zero_mul] using (Metric.summable_norm_pow D hD).tendsto_atTop_zero.mul_const ‖L‖

omit [NormOneClass A] [NormedAlgebra ℂ A] [CompleteSpace A] in
theorem finite_recurrence (D L C a : A) (hL : L = D * L * a + C) (N : ℕ) :
    L = (∑ j ∈ Finset.range N, D ^ j * C * a ^ j) + D ^ N * L * a ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ D N, pow_succ' a N]
    calc
      L = (∑ j ∈ Finset.range N, D ^ j * C * a ^ j) + D ^ N * L * a ^ N := ih
      _ = (∑ j ∈ Finset.range N, D ^ j * C * a ^ j) + D ^ N * (D * L * a + C) * a ^ N := by
        conv_lhs => arg 2; arg 1; arg 2; rw [hL]
      _ = _ := by noncomm_ring

theorem eq_two_sided_series (D L C a : A) (hD : spectralRadius ℂ D < 1)
    (ha : ‖a‖ ≤ 1) (hL : L = D * L * a + C) :
    L = ∑' j : ℕ, D ^ j * C * a ^ j := by
  have hs := summable_two_sided_series D C a hD ha
  have ht := hs.tendsto_sum_tsum_nat.add (tendsto_two_sided_remainder D L a hD ha)
  simp only [← finite_recurrence D L C a hL, add_zero] at ht
  exact tendsto_nhds_unique tendsto_const_nhds ht

theorem eq_realization_series (D L X Y a b c d : A) (hD : spectralRadius ℂ D < 1)
    (ha : ‖a‖ ≤ 1) (hL : L = D * L * a + X * c) (hY : Y = D * L * b + X * d) :
    Y = X * d + ∑' j : ℕ, D ^ (j + 1) * X * c * a ^ j * b := by
  have hs := summable_two_sided_series D (X * c) a hD ha
  rw [hY, eq_two_sided_series D L (X * c) a hD ha hL, add_comm]
  congr 1
  rw [← Summable.tsum_mul_left D hs, ← Summable.tsum_mul_right b (hs.mul_left D)]
  apply tsum_congr
  intro j
  rw [pow_succ']
  noncomm_ring

end Iteration

end CrouzeixHilbert.Realization

end

end OAI
