import Mathlib

namespace OAI

namespace PiExponent

theorem exists_large_log_approximation
    (nu X : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℤ, ∃ q : ℕ,
      2 ≤ q ∧ X < Real.log q ∧ p ≠ 0 ∧
        |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp X)
  obtain ⟨p, q, hq, happrox⟩ := hbad (max 2 N)
  have hq2 : 2 ≤ q := le_trans (le_max_left _ _) hq
  have hNq : N ≤ q := le_trans (le_max_right _ _) hq
  have hexp : Real.exp X < (q : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hNq)
  have hlog : X < Real.log q := by
    simpa using Real.log_lt_log (Real.exp_pos X) hexp
  have hp : p ≠ 0 := by
    intro hp0
    have hpow : (q : ℝ) ^ (-nu) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ q))
        (by linarith)
    have hpi : Real.pi ≤ (q : ℝ) ^ (-nu) := by
      simpa [hp0, abs_of_pos Real.pi_pos] using happrox
    have hpi2 := Real.pi_gt_three
    linarith
  exact ⟨p, q, hq2, hlog, hp, happrox⟩

end PiExponent

end OAI
