import OAI.NumberTheory.Ostmann.QuadraticCenter.WalshMoments

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem sum_even_range (l : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range (2 * l + 1), if Even i then f i else 0) =
      ∑ i ∈ Finset.range (l + 1), f (2 * i) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun i _ => 2 * i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at *
    exact ⟨by omega, even_two_mul i⟩
  · intro i hi j hj he
    omega
  · intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjr, hj⟩
    obtain ⟨i, hi⟩ := hj
    refine ⟨i, ?_, ?_⟩
    · simp only [Finset.mem_range] at *
      omega
    · omega
  · intro i hi
    rfl

theorem sign_pair_even_moment (x y : ℝ) (l : ℕ) :
    ((x + y) ^ (2 * l) + (x - y) ^ (2 * l)) / 2 =
      ∑ i ∈ Finset.range (l + 1),
        x ^ (2 * (l - i)) * y ^ (2 * i) * ((2 * l).choose (2 * i) : ℝ) := by
  have ht (i : ℕ) :
      y ^ i * x ^ (2 * l - i) * ((2 * l).choose i : ℝ) +
        (-y) ^ i * x ^ (2 * l - i) * ((2 * l).choose i : ℝ) =
      2 * (if Even i then
        x ^ (2 * l - i) * y ^ i * ((2 * l).choose i : ℝ) else 0) := by
    by_cases hi : Even i
    · rw [hi.neg_pow]
      simp only [hi, ite_true]
      ring
    · rw [(Nat.not_even_iff_odd.mp hi).neg_pow]
      simp only [hi, ite_false]
      ring
  rw [show x + y = y + x by ring, show x - y = -y + x by ring]
  rw [add_pow, add_pow, ← Finset.sum_add_distrib]
  simp_rw [ht]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    sum_even_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show 2 * l - 2 * i = 2 * (l - i) by omega]

theorem even_choose_le_scaled (l i : ℕ) :
    (2 * l).choose (2 * i) ≤ l.choose i * (2 * l) ^ (2 * i) := by
  by_cases hi : i ≤ l
  · have hc : 1 ≤ l.choose i := Nat.succ_le_iff.mpr (Nat.choose_pos hi)
    calc
      _ ≤ (2 * l) ^ (2 * i) := Nat.choose_le_pow _ _
      _ ≤ l.choose i * (2 * l) ^ (2 * i) := Nat.le_mul_of_pos_left _ hc
  · have hlt : 2 * l < 2 * i := by omega
    simp [Nat.choose_eq_zero_of_lt hlt]

theorem sign_pair_even_moment_le (x y : ℝ) (l : ℕ) :
    ((x + y) ^ (2 * l) + (x - y) ^ (2 * l)) / 2 ≤
      (x ^ 2 + (((2 * l : ℕ) : ℝ) ^ 2) * y ^ 2) ^ l := by
  rw [sign_pair_even_moment]
  calc
    _ ≤ ∑ i ∈ Finset.range (l + 1),
        x ^ (2 * (l - i)) * y ^ (2 * i) *
          ((l.choose i : ℝ) * ((2 * l : ℕ) : ℝ) ^ (2 * i)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast even_choose_le_scaled l i
      · simpa only [pow_mul] using
          mul_nonneg (pow_nonneg (sq_nonneg x) (l - i))
            (pow_nonneg (sq_nonneg y) i)
    _ = _ := by
      rw [show x ^ 2 + (((2 * l : ℕ) : ℝ) ^ 2) * y ^ 2 =
        (((2 * l : ℕ) : ℝ) ^ 2) * y ^ 2 + x ^ 2 by ring, add_pow]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [mul_pow, ← pow_mul]
      ring

end Ostmann.QuadraticCenter

end OAI
