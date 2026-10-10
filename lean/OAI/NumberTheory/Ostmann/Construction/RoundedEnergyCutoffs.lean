import OAI.NumberTheory.Ostmann.Construction.ScheduledFrequencyBounds
import OAI.NumberTheory.Ostmann.Arithmetic.LeafFrequencyBudget

namespace OAI

/-! # Numerical cutoffs for the actual square-root-reserve schedule -/

namespace Ostmann
open Filter

/-- The signed root-frequency set includes zero and both endpoints. -/
theorem card_transferFrequencyRange (V : ℕ) : (transferFrequencyRange V).card = 2 * V + 1 := by
  simp only [transferFrequencyRange, Int.card_Icc]
  omega

/-- At fixed depth the whole rounded frequency family has an exponential
bound linear in the word length, with its square-root reserve absorbed. -/
theorem eventual_rounded_frequency_card (n : ℕ) (d : ℝ) (hd : 0 ≤ d) :
    ∀ᶠ m : ℝ in atTop, ∀ j ≤ n,
      ((transferFrequencyRange (naturalTransferCutoff (d * m) m j)).card : ℝ) ≤
        Real.exp (((2 : ℝ) ^ n * d + 1) * m) := by
  obtain ⟨M, hM⟩ := sqrt_cost_sublinear (2 * (4 : ℝ) ^ n) (Real.log 3) 1
    (by positivity) (by norm_num)
  filter_upwards [eventually_ge_atTop M, eventually_ge_atTop (0 : ℝ)] with m hm hm0 j hj
  have hb := hM m hm
  have h2 : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hj
  have h4 : (4 : ℝ) ^ j ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hj
  have he : 0 ≤ transferErrorScale (d * m) m j := by unfold transferErrorScale; positivity
  have hfloor : (naturalTransferCutoff (d * m) m j : ℝ) ≤
      Real.exp (transferErrorScale (d * m) m j) := Nat.floor_le (Real.exp_pos _).le
  have hone : 1 ≤ Real.exp (transferErrorScale (d * m) m j) := Real.one_le_exp he
  rw [card_transferFrequencyRange]
  push_cast
  calc
    _ ≤ 3 * Real.exp (transferErrorScale (d * m) m j) := by linarith
    _ = Real.exp (Real.log 3 + transferErrorScale (d * m) m j) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold transferErrorScale
      have ha := mul_le_mul_of_nonneg_right h2 (mul_nonneg hd hm0)
      have hc := mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg m)
      nlinarith

/-- The rate theorem's square-root parameter is four times the actual word
length, so it covers the literal `2 sqrt(m)` bottom-frequency reserve. -/
theorem rounded_bottom_frequency_bound (Δ m : ℝ) :
    (naturalTransferCutoff Δ m 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) := by
  have h := Nat.floor_le (Real.exp_pos (transferErrorScale Δ m 0)).le
  change (naturalTransferCutoff Δ m 0 : ℝ) ≤ _
  apply h.trans_eq
  congr 1
  simp only [transferErrorScale, pow_zero, one_mul]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

end Ostmann

end OAI
