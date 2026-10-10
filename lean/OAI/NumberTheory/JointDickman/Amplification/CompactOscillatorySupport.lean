import OAI.NumberTheory.JointDickman.Amplification.ScaledOscillatoryTests
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace OAI

/-! # Removing finite cutoffs for compactly supported tests -/

namespace JointDickman

open Finset MeasureTheory

open Classical in
theorem tsum_eq_Ioc_of_scaled_support {w : ℝ → ℝ} {a b X : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hX : 0 < X)
    (hws : ∀ t, t ≤ a ∨ b < t → w t = 0)
    (f : ℕ → ℂ) (hf : ∀ n : ℕ, w (n / X) = 0 → f n = 0) :
    ∑' n, f n = ∑ n ∈ Ioc ⌊a * X⌋₊ ⌊b * X⌋₊, f n := by
  apply tsum_eq_sum
  intro n hn
  apply hf n
  apply hws
  by_cases hna : n ≤ ⌊a * X⌋₊
  · left
    exact (div_le_iff₀ hX).mpr ((Nat.le_floor_iff (mul_nonneg ha hX.le)).mp hna)
  · right
    have hnb : ⌊b * X⌋₊ < n := by
      have hn' : ¬(⌊a * X⌋₊ < n ∧ n ≤ ⌊b * X⌋₊) := by simpa only [mem_Ioc] using hn
      omega
    exact (lt_div_iff₀ hX).mpr ((Nat.floor_lt (mul_nonneg (ha.trans hab) hX.le)).mp hnb)

theorem oscillatory_integral_eq_integral {w : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hws : ∀ t, t ≤ a ∨ b < t → w t = 0)
    (ξ : ℝ) (ρ : ℝ → ℂ) :
    (∫ t in a..b, oscillatoryTest w ξ t * ρ t) =
      ∫ t, oscillatoryTest w ξ t * ρ t := by
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have h : t ≤ a ∨ b < t := by
    by_cases hta : t ≤ a
    · exact Or.inl hta
    · exact Or.inr (lt_of_not_ge (fun htb => ht ⟨lt_of_not_ge hta, htb⟩))
  simp only [oscillatoryTest, hws t h, Complex.ofReal_zero, zero_mul]

end JointDickman

end OAI
