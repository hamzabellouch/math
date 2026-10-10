import OAI.Analysis.Unitarizability.Parameters
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

/-! Ceiling dimensions and finite union-bound arithmetic for frames. -/
noncomputable section
namespace Dixmier
namespace FrameParameters

def dimension (n r : ℕ) : ℕ := ⌈2 * (r : ℝ) * Real.log (2 * (n : ℝ))⌉₊
def subfamilySize (n r : ℕ) : ℕ := min (2*r) n

theorem bounds {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) :
    1 ≤ dimension n r ∧ subfamilySize n r ≤ dimension n r ∧
      (subfamilySize n r : ℝ) * Real.log n ≤ dimension n r := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlog : 1 < Real.log (2 * (n : ℝ)) := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log (by positivity)]
    linarith [Real.exp_one_lt_three]
  have hceil : 2 * (r : ℝ) * Real.log (2 * (n : ℝ)) ≤ dimension n r := Nat.le_ceil _
  have hp : (subfamilySize n r : ℝ) ≤ 2 * r := by exact_mod_cast Nat.min_le_left (2*r) n
  have hlogn : Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log hn0 (by linarith)
  have hp0 : (0 : ℝ) ≤ subfamilySize n r := Nat.cast_nonneg _
  have hkp : (subfamilySize n r : ℝ) ≤ dimension n r := by
    have hp2 := mul_le_mul_of_nonneg_left hlog.le (by positivity : (0 : ℝ) ≤ 2 * r)
    nlinarith
  refine ⟨?_, by exact_mod_cast hkp, ?_⟩
  · have : (1 : ℝ) ≤ dimension n r := by nlinarith
    exact_mod_cast this
  · calc
      _ ≤ (subfamilySize n r : ℝ) * Real.log (2 * (n : ℝ)) := mul_le_mul_of_nonneg_left hlogn hp0
      _ ≤ 2 * (r : ℝ) * Real.log (2 * (n : ℝ)) := mul_le_mul_of_nonneg_right hp (by linarith)
      _ ≤ _ := hceil

/-- The frame failure probability is strictly below one. -/
theorem failure_bound_lt_one {n k p : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hp : p ≤ k) (hplog : (p : ℝ) * Real.log n ≤ k) :
    2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2) < 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpk : (p : ℝ) ≤ k := by exact_mod_cast hp
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl9 : Real.log 9 ≤ 4 := by
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    have h9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3^2 by norm_num, Real.log_pow]
      norm_num
    rw [h9]
    linarith
  have he : Real.log 2 + (p : ℝ)*Real.log n + ((k : ℝ)+p)*Real.log 9 -25*(k : ℝ)/2 < 0 := by
    have hh := mul_le_mul_of_nonneg_left hl9 (by positivity : (0 : ℝ) ≤ (k : ℝ)+p)
    nlinarith
  have hid : 2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2) =
      Real.exp (Real.log 2 + (p : ℝ)*Real.log n + ((k : ℝ)+p)*Real.log 9 -25*(k : ℝ)/2) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_add]
    simp only [Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_nat_mul,
      Real.exp_log hn0, ← Nat.cast_add]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 9)]
    congr 1
    ring_nf
  rw [hid]
  exact Real.exp_lt_one_iff.mpr he

theorem exact_failure_bound {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) :
    2 * (n : ℝ)^(subfamilySize n r) * 9^(dimension n r + subfamilySize n r) *
      Real.exp (-25*(dimension n r : ℝ)/2) < 1 :=
  failure_bound_lt_one hn (bounds hn hr).1 (bounds hn hr).2.1 (bounds hn hr).2.2

end FrameParameters
end Dixmier

end

end OAI
