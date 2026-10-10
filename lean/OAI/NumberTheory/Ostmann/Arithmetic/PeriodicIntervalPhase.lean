import OAI.NumberTheory.Ostmann.ZeroDensity.OriginalDensityCorrelation

namespace OAI

/-! # The periodic phase estimate on a translated integer interval -/

namespace Ostmann

open scoped BigOperators

theorem weighted_periodic_linear_shift_bound (q : ℕ) [NeZero q]
    (f : ZMod q → ℂ) (A α : ℝ) (hA : 0 ≤ A)
    (hf : ∀ u, ‖additiveFourier f u‖ ≤ A) (w : ℕ → ℂ) (M N : ℕ) :
    ‖∑ n ∈ Finset.range N, w n *
      (f ((n + M : ℕ) : ZMod q) * realAdditivePhase α ^ (n + M))‖ ≤
      discreteVariation w N * (2 * A * ((N : ℝ) + q * (1 + Real.log q))) := by
  have ht (u : ZMod q) : ‖additiveFourier (fun x => f (x + (M : ZMod q))) u‖ ≤ A := by
    rw [additiveFourier_add_right, norm_mul]
    have hc : ‖ZMod.stdAddChar ((M : ZMod q) * u)‖ = 1 := by simp [ZMod.stdAddChar_apply]
    rw [hc, one_mul]
    exact hf u
  have heq : (∑ n ∈ Finset.range N, w n *
      (f ((n + M : ℕ) : ZMod q) * realAdditivePhase α ^ (n + M))) =
      realAdditivePhase α ^ M * ∑ n ∈ Finset.range N, w n *
        ((fun x : ZMod q => f (x + (M : ZMod q))) (n : ZMod q) * realAdditivePhase α ^ n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [pow_add, Nat.cast_add]
    ring
  rw [heq, norm_mul, norm_pow, norm_realAdditivePhase, one_pow, one_mul]
  exact weighted_periodic_linear_phase_bound q _ A α hA ht w N

theorem periodic_grid_cost_le_square (q : ℕ) [NeZero q] :
    (q : ℝ) * (1 + Real.log q) ≤ (q : ℝ) ^ 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hl := Real.log_le_sub_one_of_pos hq
  nlinarith

theorem weighted_periodic_linear_shift_long_bound (q : ℕ) [NeZero q]
    (f : ZMod q → ℂ) (A α : ℝ) (hA : 0 ≤ A)
    (hf : ∀ u, ‖additiveFourier f u‖ ≤ A) (w : ℕ → ℂ) (M N : ℕ)
    (hN : q ^ 2 ≤ N) :
    ‖∑ n ∈ Finset.range N, w n *
      (f ((n + M : ℕ) : ZMod q) * realAdditivePhase α ^ (n + M))‖ ≤
      discreteVariation w N * (4 * A * N) := by
  apply (weighted_periodic_linear_shift_bound q f A α hA hf w M N).trans
  apply mul_le_mul_of_nonneg_left _ (by unfold discreteVariation; positivity)
  have hN' : (q : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hg := periodic_grid_cost_le_square q
  nlinarith

end Ostmann

end OAI
