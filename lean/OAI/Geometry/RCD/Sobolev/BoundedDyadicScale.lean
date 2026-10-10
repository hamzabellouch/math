import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace OAI

/-! # Choosing a comparison scale without passing the prescribed fine scale -/

namespace RegularPointCoordinates

/-- A distance no smaller than the prescribed fine radius has a dyadic
comparison radius at least as coarse as that radius. -/
theorem exists_bounded_dyadic_scale {R t : ℝ} (hR : 0 < R) (ht : 0 < t)
    (htR : t ≤ R) (k : ℕ) (hmin : R / (2 : ℝ) ^ k ≤ t) :
    ∃ j : ℕ, j ≤ k ∧ t ≤ R / (2 : ℝ) ^ j ∧ R / (2 : ℝ) ^ j < 2 * t := by
  obtain ⟨j, hn, hc⟩ := exists_nat_pow_near_of_lt_one (div_pos ht hR)
    ((div_le_one hR).mpr htR) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hp (i : ℕ) : (1 / 2 : ℝ) ^ i = ((2 : ℝ) ^ i)⁻¹ := by rw [one_div, inv_pow]
  have hupper : t ≤ R / (2 : ℝ) ^ j := by
    have h := (div_le_iff₀ hR).mp hc
    rw [hp j] at h
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hlower : R / (2 : ℝ) ^ j < 2 * t := by
    have h := (lt_div_iff₀ hR).mp hn
    rw [pow_succ, hp j] at h
    change ((2 : ℝ) ^ j)⁻¹ * (1 / 2) * R < t at h
    have heq : ((2 : ℝ) ^ j)⁻¹ * (1 / 2) * R = (R / (2 : ℝ) ^ j) / 2 := by ring
    rw [heq] at h
    linarith
  have hj : j ≤ k := by
    by_contra hj
    have hn : k + 1 ≤ j := by omega
    have hpowers : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hn
    have hdiv := div_le_div_of_nonneg_left hR.le (by positivity : (0 : ℝ) < 2 ^ (k + 1)) hpowers
    have heq : R / (2 : ℝ) ^ (k + 1) = (R / (2 : ℝ) ^ k) / 2 := by rw [pow_succ]; ring
    rw [heq] at hdiv
    linarith [div_pos hR (by positivity : (0 : ℝ) < 2 ^ k)]
  exact ⟨j, hj, hupper, hlower⟩

end RegularPointCoordinates

end OAI
