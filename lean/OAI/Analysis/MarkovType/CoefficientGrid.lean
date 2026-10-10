import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

namespace MarkovSuperreflexivity

noncomputable section

def coefficientGridValue (k : ℕ) (j : Fin (2 * k ^ 2 + 1)) : ℝ :=
  (j.val : ℝ) / (k : ℝ) ^ 2 - 1

theorem abs_coefficientGridValue_le (k : ℕ) (hk : 0 < k)
    (j : Fin (2 * k ^ 2 + 1)) : |coefficientGridValue k j| ≤ 1 := by
  have hq : 0 < (k : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hk) _
  have hj : j.val ≤ 2 * k ^ 2 := Nat.le_of_lt_succ j.isLt
  have hjR : (j.val : ℝ) ≤ 2 * (k : ℝ) ^ 2 := by exact_mod_cast hj
  have hlo : 0 ≤ (j.val : ℝ) / (k : ℝ) ^ 2 :=
    div_nonneg (Nat.cast_nonneg _) hq.le
  have hhi : (j.val : ℝ) / (k : ℝ) ^ 2 ≤ 2 :=
    (div_le_iff₀ hq).2 hjR
  unfold coefficientGridValue
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem exists_coefficientGrid_approx (k : ℕ) (hk : 0 < k)
    (a : ℝ) (ha : |a| ≤ 1) :
    ∃ j : Fin (2 * k ^ 2 + 1),
      |a - coefficientGridValue k j| ≤ 1 / (k : ℝ) ^ 2 := by
  have hq : 0 < (k : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hk) _
  obtain ⟨haLower, haUpper⟩ := abs_le.mp ha
  let x : ℝ := (a + 1) * (k : ℝ) ^ 2
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact mul_nonneg (by linarith) hq.le
  have hxUpper : x ≤ ((2 * k ^ 2 : ℕ) : ℝ) := by
    dsimp only [x]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_right (show a + 1 ≤ (2 : ℝ) by linarith) hq.le
  let n : ℕ := ⌊x⌋₊
  have hn : n ≤ 2 * k ^ 2 := Nat.floor_le_of_le hxUpper
  let j : Fin (2 * k ^ 2 + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  have hnDiv : (n : ℝ) / (k : ℝ) ^ 2 ≤ a + 1 :=
    (div_le_iff₀ hq).2 (Nat.floor_le hx0)
  have hNear : a + 1 < ((n : ℝ) + 1) / (k : ℝ) ^ 2 :=
    (lt_div_iff₀ hq).2 (Nat.lt_floor_add_one x)
  rw [add_div] at hNear
  refine ⟨j, ?_⟩
  change |a - ((n : ℝ) / (k : ℝ) ^ 2 - 1)| ≤ 1 / (k : ℝ) ^ 2
  rw [abs_of_nonneg (show 0 ≤ a - ((n : ℝ) / (k : ℝ) ^ 2 - 1) by linarith)]
  linarith

end

end MarkovSuperreflexivity

end OAI
