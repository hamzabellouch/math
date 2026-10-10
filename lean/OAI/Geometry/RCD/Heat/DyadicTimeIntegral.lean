import OAI.Geometry.RCD.Heat.GaussianTimeConvolution
import OAI.Geometry.RCD.Heat.HeatBlockIntegrals
import OAI.Geometry.RCD.Heat.DyadicHeatFamily

namespace OAI

/-! # Finite dyadic time decomposition for actual integrable sources -/

open Set MeasureTheory
open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- Consecutive dyadic time blocks telescope exactly. Integrability is
explicit, so no use is made of the undefined-integral zero convention. -/
theorem dyadic_time_integral_eq_sum (f : ℝ → ℝ) {R : ℝ} (hR : 0 < R) (i : ℕ)
    (hf : IntervalIntegrable f volume ((R / (2 : ℝ) ^ i) ^ 2) (R ^ 2)) :
    (∫ t in (R / (2 : ℝ) ^ i) ^ 2..R ^ 2, f t) =
      ∑ j ∈ Finset.range i, ∫ t in (R / (2 : ℝ) ^ j) ^ 2 / 4..(R / (2 : ℝ) ^ j) ^ 2, f t := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
    have hsi : (R / (2 : ℝ) ^ i) ^ 2 ≤ R ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_self hR.le (one_le_pow₀ (by norm_num))
    have hnext := dyadic_radius_square_succ R i
    rw [hnext] at hf ⊢
    have hlow : (R / (2 : ℝ) ^ i) ^ 2 / 4 ≤ (R / (2 : ℝ) ^ i) ^ 2 := by nlinarith [sq_nonneg (R / (2 : ℝ) ^ i)]
    have hleft : IntervalIntegrable f volume ((R / (2 : ℝ) ^ i) ^ 2 / 4) ((R / (2 : ℝ) ^ i) ^ 2) := hf.mono_set' (by
      rw [uIoc_of_le (hlow.trans hsi), uIoc_of_le hlow]
      exact Ioc_subset_Ioc_right hsi)
    have hright : IntervalIntegrable f volume ((R / (2 : ℝ) ^ i) ^ 2) (R ^ 2) := hf.mono_set' (by
      rw [uIoc_of_le (hlow.trans hsi), uIoc_of_le hsi]
      exact Ioc_subset_Ioc_left hlow)
    rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright,
      ih hright, Finset.sum_range_succ]
    ring

/-- A bound on each actual block gives the corresponding finite weighted
sum on the entire long-time interval. -/
theorem dyadic_time_integral_abs_le (f : ℝ → ℝ) {R : ℝ} (hR : 0 < R) (i : ℕ)
    (hf : IntervalIntegrable f volume ((R / (2 : ℝ) ^ i) ^ 2) (R ^ 2))
    (B : ℕ → ℝ) (hb : ∀ j < i,
      |∫ t in (R / (2 : ℝ) ^ j) ^ 2 / 4..(R / (2 : ℝ) ^ j) ^ 2, f t| ≤ B j) :
    |∫ t in (R / (2 : ℝ) ^ i) ^ 2..R ^ 2, f t| ≤ ∑ j ∈ Finset.range i, B j := by
  rw [dyadic_time_integral_eq_sum f hR i hf]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => hb j (Finset.mem_range.mp hj))

end RegularPointCoordinates

end

end OAI
