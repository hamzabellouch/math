import Mathlib
import OAI.Probability.SKBarriers.Dynamics.Uniformization

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem clockWeight_succ_mul (a : ℝ) (k : ℕ) :
    ((k+1:ℕ):ℝ)*clockWeight a (k+1) = a*clockWeight a k := by
  unfold clockWeight
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  have h1 : (k:ℝ)+1 ≠ 0 := by positivity
  have h2 : (k.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

theorem clockWeight_mean_hasSum (a : ℝ) : HasSum (fun k : ℕ => (k:ℝ)*clockWeight a k) a := by
  have H := (clockWeight_hasSum a).mul_left a
  rw [mul_one] at H
  have HH : HasSum (fun k : ℕ => ((k+1:ℕ):ℝ)*clockWeight a (k+1)) a := by
    simpa only [clockWeight_succ_mul] using H
  have HHH := (hasSum_nat_add_iff (f := fun k : ℕ => (k:ℝ)*clockWeight a k) (g := a) 1).mp HH
  simpa only [Finset.sum_range_one,Nat.cast_zero,zero_mul,add_zero] using HHH

theorem clockWeight_tail_summable {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    Summable (fun k : ℕ => if m < k then clockWeight a k else 0) := by
  apply Summable.of_nonneg_of_le _ _ (clockWeight_hasSum a).summable
  · intro k; split_ifs
    · exact clockWeight_nonneg ha k
    · exact le_refl 0
  · intro k; split_ifs
    · exact le_refl _
    · exact clockWeight_nonneg ha k

theorem clockWeight_tail_le {a : ℝ} (ha : 0 ≤ a) {m : ℕ} (hm : 0 < m) :
    (∑' k : ℕ, if m < k then clockWeight a k else 0) ≤ a/(m:ℝ) := by
  have H := ((clockWeight_tail_summable ha m).mul_left (m:ℝ)).tsum_le_tsum
    (fun k => show (m:ℝ)*(if m < k then clockWeight a k else 0) ≤ (k:ℝ)*clockWeight a k from by
      split_ifs with hk
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_of_lt hk) (clockWeight_nonneg ha k)
      · simp only [mul_zero]; exact mul_nonneg (by positivity) (clockWeight_nonneg ha k))
    (clockWeight_mean_hasSum a).summable
  rw [tsum_mul_left,(clockWeight_mean_hasSum a).tsum_eq] at H
  exact (le_div_iff₀ (show (0:ℝ) < m by exact_mod_cast hm)).mpr (by simpa only [mul_comm] using H)

theorem attempt_horizon_tail (n : ℕ) (L : ℝ) :
    (∑' k : ℕ, if ⌈Real.exp (2*L)⌉₊ < k then clockWeight ((n:ℝ)*Real.exp L) k else 0) ≤
      (n:ℝ)*Real.exp (-L) := by
  have hExp := Real.exp_pos (2*L)
  have hm : 0 < ⌈Real.exp (2*L)⌉₊ := Nat.ceil_pos.mpr hExp
  have hceil : Real.exp (2*L) ≤ (⌈Real.exp (2*L)⌉₊:ℝ) := Nat.le_ceil _
  calc
    _ ≤ ((n:ℝ)*Real.exp L)/(⌈Real.exp (2*L)⌉₊:ℝ) := clockWeight_tail_le (by positivity) hm
    _ ≤ ((n:ℝ)*Real.exp L)/Real.exp (2*L) := div_le_div_of_nonneg_left (by positivity) hExp hceil
    _ = (n:ℝ)*Real.exp (-L) := by
      rw [mul_div_assoc,← Real.exp_sub]
      congr 2
      ring

end SK.Analytic

end
end

end

end OAI
