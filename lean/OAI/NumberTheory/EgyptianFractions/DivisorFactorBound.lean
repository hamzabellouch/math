import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Number of positive divisors at most a real cutoff. -/
def truncatedDivisorCount (X : ℝ) (n : ℕ) : ℕ :=
  (n.divisors.filter (fun a : ℕ => (a : ℝ) ≤ X)).card

/-- Splitting a divisor at its gcd with a fixed factor loses no information. -/
theorem divisor_gcd_pair_injective (d : ℕ) :
    Function.Injective (fun a : ℕ => (Nat.gcd a d, a / Nat.gcd a d)) := by
  intro a b hab
  have h := congrArg (fun p : ℕ × ℕ => p.1 * p.2) hab
  simpa only [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)] using h

/-- The factor remaining after taking a gcd divides the complementary factor. -/
theorem divisor_div_gcd_dvd_quotient {a d n : ℕ} (ha : a ∣ n) (hd : d ∣ n) :
    a / Nat.gcd a d ∣ n / d := by
  apply (Nat.dvd_div_iff_mul_dvd hd).2
  have h := Nat.lcm_dvd ha hd
  rw [Nat.lcm_eq_mul_div, Nat.mul_comm a d,
    Nat.mul_div_assoc d (Nat.gcd_dvd_left a d)] at h
  exact h

/-- The truncated divisor count is submultiplicative across any factorization;
    the factors need not be coprime. -/
theorem truncatedDivisorCount_factor_bound (X : ℝ) {d n : ℕ} (hd : d ∣ n) :
    truncatedDivisorCount X n ≤ d.divisors.card * truncatedDivisorCount X (n / d) := by
  by_cases hn : n = 0
  · simp [truncatedDivisorCount, hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hnpos
  have hquot : n / d ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hnpos hd) hdpos)
  unfold truncatedDivisorCount
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun a : ℕ => (Nat.gcd a d, a / Nat.gcd a d))
  · intro a ha
    obtain ⟨ha, haX⟩ := Finset.mem_filter.mp ha
    have hadvd : a ∣ n := (Nat.mem_divisors.mp ha).1
    apply Finset.mem_product.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right a d, Nat.ne_of_gt hdpos⟩
    · apply Finset.mem_filter.mpr
      constructor
      · exact Nat.mem_divisors.mpr ⟨divisor_div_gcd_dvd_quotient hadvd hd, hquot⟩
      · exact le_trans (by exact_mod_cast Nat.div_le_self a (Nat.gcd a d)) haX
  · exact (divisor_gcd_pair_injective d).injOn

end Problem337

end

end OAI
