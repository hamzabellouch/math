import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.RelativeScaleBudget

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem relativeScaleBudget_le_log (s : ℕ → ℝ) (T : ℕ)
    (hs : ∀ k ≤ T, 0 < s k)
    (hdec : ∀ k < T, s (k+1) ≤ s k)
    (hratio : ∀ k < T, s k ≤ 2*s (k+1)) :
    relativeScaleBudget s T ≤ 2*Real.log (s 0/s T) := by
  have hsingle {r : ℝ} (h1 : 1 ≤ r) (h2 : r ≤ 2) : r-1 ≤ 2*Real.log r := by
    have hr : 0 < r := lt_of_lt_of_le zero_lt_one h1
    have hi : 0 ≤ 1-r⁻¹ := sub_nonneg.mpr ((inv_le_one₀ hr).mpr h1)
    calc
      r-1 = r*(1-r⁻¹) := by field_simp
      _ ≤ 2*(1-r⁻¹) := mul_le_mul_of_nonneg_right h2 hi
      _ ≤ 2*Real.log r := mul_le_mul_of_nonneg_left
        (Real.one_sub_inv_le_log_of_pos hr) (by norm_num)
  have htel : (∑ k ∈ Finset.range T, Real.log (s k/s (k+1))) =
      Real.log (s 0/s T) := by
    calc
      _ = ∑ k ∈ Finset.range T, (Real.log (s k)-Real.log (s (k+1))) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkT := Finset.mem_range.mp hk
        exact Real.log_div (ne_of_gt (hs k (by omega)))
          (ne_of_gt (hs (k+1) (by omega)))
      _ = Real.log (s 0)-Real.log (s T) := by rw [Finset.sum_range_sub']
      _ = Real.log (s 0/s T) := (Real.log_div
        (ne_of_gt (hs 0 (Nat.zero_le T))) (ne_of_gt (hs T le_rfl))).symm
  rw [← htel,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkT := Finset.mem_range.mp hk
  exact hsingle ((one_le_div (hs (k+1) (by omega))).mpr (hdec k hkT))
    ((div_le_iff₀ (hs (k+1) (by omega))).mpr (hratio k hkT))

end SharpTerminalLeave

end

end OAI
