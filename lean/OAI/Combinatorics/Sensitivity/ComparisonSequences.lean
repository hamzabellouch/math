import OAI.Combinatorics.Sensitivity.ScalarBounds

namespace OAI

/-! Comparison sequences, a telescoping sum, and geometric estimates. -/

noncomputable section
open scoped BigOperators

namespace Paper320

def comparisonPair (ε L : ℝ) : ℕ → ℝ × ℝ
  | 0 => (L, 0)
  | n + 1 =>
      let p := comparisonPair ε L n
      ((1 + ε) * p.1 + 3 * p.2, ε * p.1 + 3 * p.2)

def comparisonU (ε L : ℝ) (n : ℕ) : ℝ := (comparisonPair ε L n).1
def comparisonV (ε L : ℝ) (n : ℕ) : ℝ := (comparisonPair ε L n).2

@[simp] theorem comparisonU_zero (ε L : ℝ) : comparisonU ε L 0 = L := rfl
@[simp] theorem comparisonV_zero (ε L : ℝ) : comparisonV ε L 0 = 0 := rfl
theorem comparisonU_succ (ε L : ℝ) (n : ℕ) :
    comparisonU ε L (n + 1) = (1 + ε) * comparisonU ε L n + 3 * comparisonV ε L n := rfl
theorem comparisonV_succ (ε L : ℝ) (n : ℕ) :
    comparisonV ε L (n + 1) = ε * comparisonU ε L n + 3 * comparisonV ε L n := rfl

theorem comparison_nonneg {ε L : ℝ} (hε : 0 ≤ ε) (hL : 0 ≤ L) (n : ℕ) :
    0 ≤ comparisonU ε L n ∧ 0 ≤ comparisonV ε L n := by
  induction n with
  | zero => simpa using hL
  | succ n ih =>
      obtain ⟨hu, hv⟩ := ih
      rw [comparisonU_succ, comparisonV_succ]
      constructor <;> positivity

theorem profiles_le_comparison (d : ℕ) (u v : ℕ → ℝ) (ε L : ℝ) (hε : 0 ≤ ε)
    (hu0 : u 0 ≤ L) (hv0 : v 0 ≤ 0)
    (hu : ∀ n < d, u (n + 1) ≤ (1 + ε) * u n + 3 * v n)
    (hv : ∀ n < d, v (n + 1) ≤ ε * u n + 3 * v n) :
    ∀ n ≤ d, u n ≤ comparisonU ε L n ∧ v n ≤ comparisonV ε L n := by
  intro n
  induction n with
  | zero => intro _; exact ⟨hu0, hv0⟩
  | succ n ih =>
      intro hn
      obtain ⟨hun, hvn⟩ := ih (by omega)
      rw [comparisonU_succ, comparisonV_succ]
      constructor
      · exact (hu n (by omega)).trans
          (add_le_add (mul_le_mul_of_nonneg_left hun (by linarith))
            (mul_le_mul_of_nonneg_left hvn (by norm_num)))
      · exact (hv n (by omega)).trans
          (add_le_add (mul_le_mul_of_nonneg_left hun hε)
            (mul_le_mul_of_nonneg_left hvn (by norm_num)))

theorem comparison_bounds (d : ℕ) (ε L : ℝ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hbudget : ε * 3 ^ (d + 1) ≤ 2) :
    ∀ n ≤ d, comparisonU ε L n ≤ 2 * L ∧
      comparisonV ε L n ≤ ε * L * (3 ^ n - 1) := by
  apply coupled_profiles_bound d (comparisonU ε L) (comparisonV ε L) ε L hε hL hbudget
  · exact le_rfl
  · exact le_rfl
  · intro n _; exact le_rfl
  · intro n _; exact le_rfl

theorem comparisonU_sum (ε L : ℝ) (n : ℕ) :
    comparisonU ε L n = L + ∑ j ∈ Finset.range n,
      (ε * comparisonU ε L j + 3 * comparisonV ε L j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [comparisonU_succ, Finset.sum_range_succ]
      linarith

theorem geometric_sum_sub_one (n : ℕ) :
    (∑ j ∈ Finset.range n, ((3 : ℝ) ^ j - 1)) = (3 ^ n - 1) / 2 - n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      ring

theorem comparisonU_sum_bound {d n : ℕ} (hn : n ≤ d) {ε L : ℝ}
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hbudget : ε * 3 ^ (d + 1) ≤ 2) :
    comparisonU ε L n ≤ L + 2 * ε * L * n +
      3 * ε * L * ∑ j ∈ Finset.range n, ((3 : ℝ) ^ j - 1) := by
  rw [comparisonU_sum]
  have hs : (∑ j ∈ Finset.range n,
      (ε * comparisonU ε L j + 3 * comparisonV ε L j)) ≤
      ∑ j ∈ Finset.range n, (2 * ε * L + 3 * ε * L * (3 ^ j - 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hu, hv⟩ := comparison_bounds d ε L hε hL hbudget j
      (Nat.le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hj) hn))
    nlinarith [mul_le_mul_of_nonneg_left hu hε]
  calc
    _ ≤ L + ∑ j ∈ Finset.range n, (2 * ε * L + 3 * ε * L * (3 ^ j - 1)) := by linarith
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring

theorem comparisonU_refined {d n : ℕ} (hn : n ≤ d) {ε L : ℝ}
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hbudget : ε * 3 ^ (d + 1) ≤ 2) :
    comparisonU ε L n ≤ L + ε * L * ((3 / 2 : ℝ) * (3 ^ n - 1) - n) := by
  have h := comparisonU_sum_bound hn hε hL hbudget
  rw [geometric_sum_sub_one] at h
  nlinarith

theorem refined_error_lt_one {d n : ℕ} (hn : n ≤ d) {ε : ℝ}
    (hε : 0 ≤ ε) (hbudget : ε * 3 ^ (d + 1) ≤ 2) :
    ε * ((3 / 2 : ℝ) * (3 ^ n - 1) - n) < 1 := by
  have hp : (3 : ℝ) ^ (n + 1) ≤ 3 ^ (d + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ hn)
  have hb := (mul_le_mul_of_nonneg_left hp hε).trans hbudget
  rw [pow_succ] at hb
  rcases eq_or_lt_of_le hε with he | he
  · rw [← he]; norm_num
  · have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [mul_nonneg hε hnn]

theorem comparisonU_lt_two {d n : ℕ} (hn : n ≤ d) {ε L : ℝ}
    (hε : 0 ≤ ε) (hL : 0 < L) (hbudget : ε * 3 ^ (d + 1) ≤ 2) :
    comparisonU ε L n < 2 * L := by
  have h := comparisonU_refined hn hε hL.le hbudget
  have he := mul_lt_mul_of_pos_right (refined_error_lt_one hn hε hbudget) hL
  nlinarith

end Paper320

end

end OAI
