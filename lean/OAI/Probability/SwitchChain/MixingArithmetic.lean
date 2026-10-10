import Mathlib

namespace OAI

noncomputable section

namespace Problem315

theorem card_simpleGraph_le_two_pow_square (n : ℕ) :
    Fintype.card (SimpleGraph (Fin n)) ≤ 2 ^ (n * n) := by
  classical
  let encode : SimpleGraph (Fin n) → Fin n → Fin n → Bool :=
    fun G u v => decide (G.Adj u v)
  have hinj : Function.Injective encode := by
    intro G H h
    apply SimpleGraph.ext
    funext u v
    apply propext
    have huv := congrFun (congrFun h u) v
    simpa [encode] using huv
  have h := Fintype.card_le_of_injective encode hinj
  simpa [Fintype.card_fun, pow_mul] using h

theorem switch_denominator_le_pow_six (n : ℕ) :
    24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ) ≤ (n : ℝ) ^ 6 := by
  have h := Nat.choose_le_pow_div (α := ℝ) 4 n
  norm_num at h
  nlinarith [sq_nonneg (n : ℝ)]

theorem exponential_tv_bound_at_polynomial_time (n s : ℕ)
    (hn : 4 ≤ n) (hs : s ≤ 2 ^ (n * n)) :
    Real.sqrt (s : ℝ) / 2 *
      Real.exp (- ((2 * n ^ 8 : ℕ) : ℝ) /
        (24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ))) ≤ (1 : ℝ) / 4 := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hchoose : 0 < (n.choose 4 : ℝ) := by exact_mod_cast Nat.choose_pos hn
  have hdenom : 0 < 24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ) := by positivity
  have hratio : 2 * (n : ℝ) ^ 2 ≤
      ((2 * n ^ 8 : ℕ) : ℝ) / (24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ)) := by
    apply (le_div_iff₀ hdenom).2
    calc
      2 * (n : ℝ) ^ 2 * (24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ))
          ≤ 2 * (n : ℝ) ^ 2 * (n : ℝ) ^ 6 :=
        mul_le_mul_of_nonneg_left (switch_denominator_le_pow_six n) (by positivity)
      _ = ((2 * n ^ 8 : ℕ) : ℝ) := by push_cast; ring
  have hsqrt : Real.sqrt (s : ℝ) ≤ Real.exp ((n : ℝ) ^ 2) := by
    have hsqrt' : Real.sqrt (s : ℝ) ≤ (s : ℝ) := by
      apply Real.sqrt_le_self_iff.mpr
      rcases Nat.eq_zero_or_pos s with h | h
      · left; simp [h]
      · right; exact_mod_cast h
    calc
      Real.sqrt (s : ℝ) ≤ (s : ℝ) := hsqrt'
      _ ≤ (2 : ℝ) ^ (n * n) := by exact_mod_cast hs
      _ ≤ Real.exp 1 ^ (n * n) :=
        pow_le_pow_left₀ (by norm_num) (by have := Real.add_one_le_exp (1 : ℝ); linarith) _
      _ = Real.exp ((n : ℝ) ^ 2) := by rw [Real.exp_one_pow]; congr 1; push_cast; ring
  have hexp : Real.exp (- ((2 * n ^ 8 : ℕ) : ℝ) /
      (24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ))) ≤ Real.exp (-2 * (n : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hsmall : Real.exp (-((n : ℝ) ^ 2)) ≤ (1 : ℝ) / 2 := by
    have hlarge : (2 : ℝ) ≤ Real.exp ((n : ℝ) ^ 2) := by
      have := Real.add_one_le_exp ((n : ℝ) ^ 2)
      nlinarith
    simpa [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlarge
  calc
    Real.sqrt (s : ℝ) / 2 * Real.exp (- ((2 * n ^ 8 : ℕ) : ℝ) /
        (24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ)))
        ≤ Real.exp ((n : ℝ) ^ 2) / 2 * Real.exp (-2 * (n : ℝ) ^ 2) := by
      exact mul_le_mul (div_le_div_of_nonneg_right hsqrt (by norm_num)) hexp
        (Real.exp_nonneg _) (by positivity)
    _ = Real.exp (-((n : ℝ) ^ 2)) / 2 := by
      rw [div_mul_eq_mul_div, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (1 : ℝ) / 4 := by linarith

end Problem315

end

end OAI
