import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace PiExponent

noncomputable def integerDistance (x : ℝ) : ℝ := |x - (round x : ℝ)|

theorem integerDistance_nonneg (x : ℝ) : 0 ≤ integerDistance x := abs_nonneg _

theorem integerDistance_le (x : ℝ) (p : ℤ) : integerDistance x ≤ |x - p| :=
  round_le x p

theorem integerDistance_le_half (x : ℝ) : integerDistance x ≤ 1 / 2 :=
  abs_sub_round x

theorem integerDistance_mul_pos {α : ℝ} (hα : Irrational α) {q : ℕ}
    (hq : 0 < q) : 0 < integerDistance (q * α) := by
  exact abs_pos.mpr (sub_ne_zero.mpr ((hα.natCast_mul hq.ne').ne_int _))

theorem finite_relative_lower_bound (f g : ℕ → ℝ)
    (hf : ∀ n, 0 < f n) (hg : ∀ n, 0 < g n) (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ n < N, c * g n ≤ f n := by
  induction N with
  | zero => exact ⟨1, zero_lt_one, le_rfl, by simp⟩
  | succ N ih =>
    rcases ih with ⟨c, hc, hc1, hbound⟩
    refine ⟨min c (f N / g N), lt_min hc (div_pos (hf N) (hg N)),
      (min_le_left _ _).trans hc1, ?_⟩
    intro n hn
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (hg n).le).trans (hbound n hn)
    · exact (le_div_iff₀ (hg n)).mp (min_le_right _ _)

theorem uniform_relative_lower_bound (f g : ℕ → ℝ)
    (hf : ∀ n, 0 < f n) (hg : ∀ n, 0 < g n)
    (htail : ∃ N : ℕ, ∀ n, N ≤ n → g n ≤ f n) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ n, c * g n ≤ f n := by
  rcases htail with ⟨N, hN⟩
  rcases finite_relative_lower_bound f g hf hg N with ⟨c, hc, hc1, hbound⟩
  refine ⟨c, hc, hc1, fun n => ?_⟩
  by_cases hn : n < N
  · exact hbound n hn
  · exact (mul_le_of_le_one_left (hg n).le hc1).trans (hN n (Nat.le_of_not_gt hn))

theorem integerDistance_lower_bound {α ν : ℝ} {q : ℕ} (hq : 0 < q)
    (h : ∀ p : ℤ, (q : ℝ) ^ (-ν) ≤ |α - p / (q : ℝ)|) :
    (q : ℝ) ^ (1 - ν) ≤ integerDistance (q * α) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh := mul_le_mul_of_nonneg_left (h (round ((q : ℝ) * α))) hqR.le
  have heq : (q : ℝ) * |α - (round ((q : ℝ) * α) : ℝ) / q| =
      integerDistance (q * α) := by
    calc
      _ = |(q : ℝ) * (α - (round ((q : ℝ) * α) : ℝ) / q)| := by
        rw [abs_mul, abs_of_pos hqR]
      _ = integerDistance (q * α) := by
        unfold integerDistance
        congr 1
        field_simp
  rw [heq] at hh
  simpa only [sub_eq_add_neg, Real.rpow_add hqR, Real.rpow_one] using hh

theorem uniform_integerDistance_lower_bound {α ν : ℝ} (hα : Irrational α)
    (h : ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 0 < q →
      ∀ p : ℤ, (q : ℝ) ^ (-ν) ≤ |α - p / (q : ℝ)|) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - ν) ≤ integerDistance (q * α) := by
  let f : ℕ → ℝ := fun n => integerDistance ((n + 1 : ℕ) * α)
  let g : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) ^ (1 - ν)
  have hf : ∀ n, 0 < f n := fun n => integerDistance_mul_pos hα (Nat.succ_pos n)
  have hg : ∀ n, 0 < g n := fun n => Real.rpow_pos_of_pos (by positivity) _
  have htail : ∃ N : ℕ, ∀ n, N ≤ n → g n ≤ f n := by
    rcases h with ⟨Q, hQ⟩
    exact ⟨Q, fun n hn => integerDistance_lower_bound (Nat.succ_pos n)
      (hQ (n + 1) (Nat.le_trans hn (Nat.le_succ n)) (Nat.succ_pos n))⟩
  rcases uniform_relative_lower_bound f g hf hg htail with ⟨c, hc, hc1, hbound⟩
  refine ⟨c, hc, hc1, ?_⟩
  rintro (_ | q) hq
  · exact False.elim (Nat.not_lt_zero _ hq)
  · exact hbound q

end PiExponent

end OAI
