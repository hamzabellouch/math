import OAI.MathematicalPhysics.DefocusingNLS.Profile.CompactifiedSlowSmoothness
import Mathlib.Analysis.Calculus.Taylor

namespace OAI

/-! # All-order outgoing asymptotics on the closed right half-plane

Taylor expansion of the actual compactified integral gives a remainder
uniform in the argument, including the nonzero imaginary boundary.
-/

open Set

namespace DefocusingNLS

noncomputable def slowAsymptoticPolynomial (q : ℂ) (m n : ℕ) (x : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), ((j.factorial : ℝ)⁻¹) • (slowAsymptoticJet q m j / x ^ j)

theorem compactifiedSlowSolution_uniform_bound (q : ℂ) (m : ℕ) (hq : -1 < q.re) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℂ, 0 ≤ x.re → 1 ≤ ‖x‖ →
      ∀ t ∈ Icc (0 : ℝ) 1, ‖compactifiedSlowSolution q m x t‖ ≤ C := by
  obtain ⟨A, hA, hb⟩ := normalizedSlowSolution_bounded q m hq
  refine ⟨max A 1, le_max_right _ _, ?_⟩
  intro x hx hn t ht
  by_cases ht0 : t = 0
  · simpa only [ht0, compactifiedSlowSolution_zero, norm_one] using le_max_right A 1
  · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    rw [compactifiedSlowSolution_pos q m x htp]
    apply (hb (x / (t : ℂ)) (slow_div_real_re_nonneg hx htp) ?_).trans (le_max_left _ _)
    rw [norm_div, Complex.norm_of_nonneg ht.1]
    exact (le_div_iff₀ htp).mpr (by linarith [ht.2])

theorem taylorWithinEval_compactifiedSlowSolution (n : ℕ) (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    taylorWithinEval (compactifiedSlowSolution q m x) n (Icc 0 1) 0 1 =
      slowAsymptoticPolynomial q m n x := by
  rw [taylor_within_apply]
  unfold slowAsymptoticPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDerivWithin_compactifiedSlowSolution_zero j q m x hq hx hx0]
  simp only [sub_zero, one_pow, mul_one]

/-- For every finite order the normalized defining integral has a uniform
inverse-power expansion, rather than just a formal series. -/
theorem regularizedSlowSolution_allOrders_remainder (n : ℕ) (q : ℂ) (m : ℕ)
    (hq : -1 < q.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 0 ≤ x.re → 1 ≤ ‖x‖ →
      ‖normalizedSlowSolution q m x - slowAsymptoticPolynomial q m n x‖ ≤
        C / ‖x‖ ^ (n + 1) := by
  have hqn : -1 < (q + (n + 1 : ℕ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) (n + 1)]
  obtain ⟨A, hA, hbound⟩ := compactifiedSlowSolution_uniform_bound
    (q + (n + 1 : ℕ)) m hqn
  let C := ‖slowAsymptoticJet q m (n + 1)‖ * A
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro x hx hn
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (zero_lt_one.trans_le hn).ne'
  have hf := (contDiffOn_compactifiedSlowSolution (n + 1) q m x hq hx hx0).mono
    (show Icc (0 : ℝ) 1 ⊆ Ici 0 from fun _ ht => ht.1)
  have hD : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (n + 1) (compactifiedSlowSolution q m x) (Icc 0 1) t‖ ≤
        C / ‖x‖ ^ (n + 1) := by
    intro t ht
    rw [iteratedDerivWithin_compactifiedSlowSolution (n + 1) q m x hq hx hx0 ht,
      norm_mul, norm_div, norm_pow]
    calc
      _ ≤ (‖slowAsymptoticJet q m (n + 1)‖ / ‖x‖ ^ (n + 1)) * A :=
        mul_le_mul_of_nonneg_left (hbound x hx hn t ht) (by positivity)
      _ = C / ‖x‖ ^ (n + 1) := by dsimp [C]; ring
  have ht := taylor_mean_remainder_bound (f := compactifiedSlowSolution q m x)
    (by norm_num : (0 : ℝ) ≤ 1) hf (show (1 : ℝ) ∈ Icc 0 1 from ⟨by norm_num, le_rfl⟩) hD
  rw [taylorWithinEval_compactifiedSlowSolution n q m x hq hx hx0] at ht
  simp only [compactifiedSlowSolution, ite_eq_right one_ne_zero, Complex.ofReal_one,
    div_one, sub_zero, one_pow, mul_one] at ht
  apply ht.trans
  apply div_le_self (div_nonneg hC (by positivity))
  have hf : (1 : ℕ) ≤ n.factorial := Nat.factorial_pos n
  exact_mod_cast hf

end DefocusingNLS

end OAI
