import OAI.Analysis.LipschitzHilbert.Estimates.GeometricScaleWeights
import Mathlib.Data.Finset.Max

namespace OAI

/-! The reciprocal lengths of the scales longer than an interval form a
geometric sum controlled by that interval's reciprocal length. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem sum_two_powers (N : ℕ) :
    (∑ j ∈ Finset.range N, (2 : ℝ) ^ j) = 2 ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem sum_long_dyadic_reciprocals (N : ℕ) (L r : ℝ) (hL : 0 < L) (hr : 0 < r) :
    (∑ j : Fin N, if r < L / (2 : ℝ) ^ j.val then
      (L / (2 : ℝ) ^ j.val)⁻¹ else 0) ≤ 2 / r := by
  classical
  change (∑ j : Fin N, (fun n : ℕ => if r < L / (2 : ℝ) ^ n then
    (L / (2 : ℝ) ^ n)⁻¹ else 0) j.val) ≤ 2 / r
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => if r < L / (2 : ℝ) ^ n then
    (L / (2 : ℝ) ^ n)⁻¹ else 0) N, ← Finset.sum_filter]
  let s := (Finset.range N).filter (fun j => r < L / (2 : ℝ) ^ j)
  change (∑ j ∈ s, (L / (2 : ℝ) ^ j)⁻¹) ≤ 2 / r
  by_cases hs : s.Nonempty
  · let m := s.max' hs
    have hm : m ∈ s := s.max'_mem hs
    have hsub : s ⊆ Finset.range (m + 1) := by
      intro j hj
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (s.le_max' j hj))
    have hbound : r * (2 : ℝ) ^ m < L :=
      (lt_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) m)).mp (Finset.mem_filter.mp hm).2
    calc
      _ ≤ ∑ j ∈ Finset.range (m + 1), (L / (2 : ℝ) ^ j)⁻¹ := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
      _ = ((2 : ℝ) ^ (m + 1) - 1) / L := by
        simp only [inv_div, ← Finset.sum_div, sum_two_powers]
      _ ≤ 2 / r := by
        apply (div_le_div_iff₀ hL hr).mpr
        rw [pow_succ]
        nlinarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hempty, Finset.sum_empty]
    positivity

end LipschitzHilbert

end

end OAI
