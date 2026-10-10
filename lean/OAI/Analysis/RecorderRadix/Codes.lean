import Mathlib
import OAI.Analysis.RecorderRadix.Intervals

namespace OAI

/-! Infinite radix codes and exact rational values for eventually constant tails. -/

namespace Solenoidal
namespace Radix
noncomputable def code {m : ℕ} (s : ℕ → Fin (m + 1)) : ℝ :=
  ∑' j : ℕ, digit (s j) * (base m)⁻¹ ^ (j + 1)

theorem inv_base_lt_one (m : ℕ) : (base m)⁻¹ < 1 := by
  apply (inv_lt_one₀ (base_pos m)).mpr
  have := base_three_le m
  linarith

theorem summable_majorant (m : ℕ) :
    Summable (fun j : ℕ => (base m - 1) * (base m)⁻¹ ^ (j + 1)) :=
  ((summable_nat_add_iff 1).mpr
    (summable_geometric_of_lt_one (inv_nonneg.mpr (base_pos m).le) (inv_base_lt_one m))).mul_left _

theorem tsum_majorant (m : ℕ) :
    ∑' j : ℕ, (base m - 1) * (base m)⁻¹ ^ (j + 1) = 1 := by
  simp_rw [pow_succ', ← mul_assoc]
  rw [tsum_mul_left, tsum_geometric_of_lt_one
    (inv_nonneg.mpr (base_pos m).le) (inv_base_lt_one m)]
  have hb : base m ≠ 0 := (base_pos m).ne'
  have hi : 1 - (base m)⁻¹ ≠ 0 := sub_ne_zero.mpr (ne_of_gt (inv_base_lt_one m))
  have hb1 : base m - 1 ≠ 0 := by have := base_three_le m; linarith
  field_simp [hb, hb1]

theorem summable_code {m : ℕ} (s : ℕ → Fin (m + 1)) :
    Summable (fun j : ℕ => digit (s j) * (base m)⁻¹ ^ (j + 1)) := by
  apply (summable_majorant m).of_nonneg_of_le
  · intro j
    exact mul_nonneg (le_trans (by norm_num) (digit_bounds (s j)).1)
      (pow_nonneg (inv_nonneg.mpr (base_pos m).le) _)
  · intro j
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr (base_pos m).le) _)
    have := (digit_bounds (s j)).2
    linarith

theorem code_bounds {m : ℕ} (s : ℕ → Fin (m + 1)) : code s ∈ Set.Icc 0 1 := by
  constructor
  · apply tsum_nonneg
    intro j
    exact mul_nonneg (le_trans (by norm_num) (digit_bounds (s j)).1)
      (pow_nonneg (inv_nonneg.mpr (base_pos m).le) _)
  · rw [code, ← tsum_majorant m]
    apply (summable_code s).tsum_le_tsum _ (summable_majorant m)
    intro j
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr (base_pos m).le) _)
    have := (digit_bounds (s j)).2
    linarith

 
theorem code_unfold {m : ℕ} (s : ℕ → Fin (m + 1)) :
    code s = pushDigit (s 0) (code (fun j => s (j + 1))) := by
  rw [code, (summable_code s).tsum_eq_zero_add]
  have ht : (∑' j : ℕ, digit (s (j + 1)) * (base m)⁻¹ ^ (j + 1 + 1)) =
      (base m)⁻¹ * code (fun j => s (j + 1)) := by
    rw [code, ← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [pow_succ]
    ring
  rw [ht]
  simp only [zero_add, pow_one, pushDigit, div_eq_mul_inv]
  ring

theorem code_mem_first {m : ℕ} (s : ℕ → Fin (m + 1)) : code s ∈ first (s 0) := by
  rw [code_unfold, first, Set.mem_Icc]
  exact ⟨(prefix_le_prefix_iff _).mpr (code_bounds _).1,
    (prefix_le_prefix_iff _).mpr (code_bounds _).2⟩

@[simp] theorem pop_code {m : ℕ} (s : ℕ → Fin (m + 1)) :
    pop (s 0) (code s) = code (fun j => s (j + 1)) := by
  rw [code_unfold s, pop_prefix]

 
theorem code_constant {m : ℕ} (a : Fin (m + 1)) :
    code (fun _ => a) = digit a / (base m - 1) := by
  have h := code_unfold (fun _ : ℕ => a)
  have hb : base m - 1 ≠ 0 := by have := base_three_le m; linarith
  dsimp [pushDigit] at h
  apply (eq_div_iff hb).mpr
  have h' := (eq_div_iff (base_pos m).ne').mp h
  linarith

 

theorem code_eventually_constant {m : ℕ} (s : ℕ → Fin (m + 1)) (a : Fin (m + 1))
    (n : ℕ) (h : ∀ j, n ≤ j → s j = a) :
    code s = (∑ j ∈ Finset.range n, digit (s j) * (base m)⁻¹ ^ (j + 1)) +
      (base m)⁻¹ ^ n * (digit a / (base m - 1)) := by
  rw [code, ← (summable_code s).sum_add_tsum_nat_add n]
  congr 1
  rw [← code_constant a, code, ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [h (j + n) (by omega), show j + n + 1 = (j + 1) + n by omega, pow_add]
  ring

 
def cons {m : ℕ} (a : Fin (m + 1)) (s : ℕ → Fin (m + 1)) : ℕ → Fin (m + 1)
  | 0 => a
  | n + 1 => s n

@[simp] theorem code_cons {m : ℕ} (a : Fin (m + 1)) (s : ℕ → Fin (m + 1)) :
    code (cons a s) = pushDigit a (code s) := code_unfold (cons a s)

def finiteCode {m : ℕ} (s : ℕ → Fin (m + 1)) (blank : Fin (m + 1)) (n : ℕ) : ℚ :=
  let B : ℚ := 2 * ((m : ℚ) + 1) + 1
  let d : Fin (m + 1) → ℚ := fun a => 2 * (a.val : ℚ) + 1
  (∑ j ∈ Finset.range n, d (s j) * B⁻¹ ^ (j + 1)) + B⁻¹ ^ n * (d blank / (B - 1))

 
theorem code_is_finiteCode {m : ℕ} (s : ℕ → Fin (m + 1)) (a : Fin (m + 1))
    (n : ℕ) (h : ∀ j, n ≤ j → s j = a) : code s = (finiteCode s a n : ℝ) := by
  rw [code_eventually_constant s a n h]
  simp [finiteCode, base, digit]
end Radix
end Solenoidal

end OAI
