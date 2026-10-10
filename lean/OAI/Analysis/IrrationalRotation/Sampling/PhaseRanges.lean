import Mathlib

namespace OAI

namespace Invariant233

theorem threshold_mem_Icc_of_abs_bounds {a x : ℝ}
    (ha : 0 < a) (hlo : a ≤ |x|) (hhi : |x| ≤ 1 / 2) :
    1 - Int.fract x ∈ Set.Icc a (1 - a) := by
  rcases le_or_gt 0 x with hx | hx
  · have habs : |x| = x := abs_of_nonneg hx
    have hfract : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx, by linarith⟩
    rw [hfract]
    constructor <;> linarith
  · have habs : |x| = -x := abs_of_neg hx
    have hfract : Int.fract (-x) = -x :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hnz : Int.fract (-x) ≠ 0 := by rw [hfract]; linarith
    have heq := Int.fract_neg hnz
    simp only [neg_neg] at heq
    rw [heq, hfract]
    constructor <;> linarith

theorem phase_small_window {m K G α k : ℝ}
    (hm : 0 < m) (hK : 0 < K) (hG : 0 < G)
    (hαlo : 1 / (m * K) ≤ α) (hαhi : α ≤ 2 / (m * K))
    (hklo : G * K ≤ |k|) (hkhi : |k| ≤ m * K / 4) :
    1 - Int.fract (k * α) ∈ Set.Icc (G / m) (1 - G / m) := by
  have hmK : 0 < m * K := mul_pos hm hK
  have hα : 0 < α := lt_of_lt_of_le (one_div_pos.mpr hmK) hαlo
  have hlo' : G / m ≤ |k| * α := by
    calc
      G / m = (G * K) * (1 / (m * K)) := by field_simp
      _ ≤ |k| * α := mul_le_mul hklo hαlo (le_of_lt (one_div_pos.mpr hmK))
        (abs_nonneg k)
  have hhi' : |k| * α ≤ 1 / 2 := by
    calc
      |k| * α ≤ (m * K / 4) * (2 / (m * K)) :=
        mul_le_mul hkhi hαhi (le_of_lt hα) (by positivity)
      _ = 1 / 2 := by field_simp; ring
  apply threshold_mem_Icc_of_abs_bounds (div_pos hG hm)
  · simpa only [abs_mul, abs_of_pos hα] using hlo'
  · simpa only [abs_mul, abs_of_pos hα] using hhi'

end Invariant233

end OAI
