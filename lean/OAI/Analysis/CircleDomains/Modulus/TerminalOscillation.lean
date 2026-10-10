import OAI.Analysis.CircleDomains.Topology.TerminalDisks

namespace OAI

/-!
# Summing the terminal oscillation errors

The simultaneous boundary estimate `A ≤ a + 4h` on finitely many
terminal disks gives the required square-sum error `4h√J`. Singular
indices can be omitted by using any subfamily of the terminal indices.
-/

open Set

namespace CircleDomainRigidity.FiniteTransfer

theorem sqrt_sum_terminal_excess_sq_le {I : Type*} (S : Finset I)
    (A a : I → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hA : ∀ s ∈ S, A s ≤ a s + 4 * h) :
    Real.sqrt (∑ s ∈ S, max (A s - a s) 0 ^ 2) ≤
      4 * h * Real.sqrt (S.card : ℝ) := by
  have hsum : (∑ s ∈ S, max (A s - a s) 0 ^ 2) ≤ (S.card : ℝ) * (4 * h) ^ 2 := by
    calc
      _ ≤ ∑ _s ∈ S, (4 * h) ^ 2 := by
        apply Finset.sum_le_sum
        intro s hs
        have hb : max (A s - a s) 0 ≤ 4 * h :=
          max_le (by linarith [hA s hs]) (by positivity)
        exact pow_le_pow_left₀ (le_max_right _ _) hb 2
      _ = _ := by simp [nsmul_eq_mul]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  calc
    _ ≤ (S.card : ℝ) * (4 * h) ^ 2 := hsum
    _ = (4 * h * Real.sqrt (S.card : ℝ)) ^ 2 := by
      simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg S.card)]
      ring

/-- The terminal-count selection directly gives the finite-transfer
oscillation budget for every nonsingular subfamily. -/
theorem sqrt_sum_terminal_excess_sq_lt {I : Type*} (S T : Finset I)
    (hST : S ⊆ T) (A a : I → ℝ) {h η : ℝ} (hh : 0 ≤ h)
    (hA : ∀ s ∈ S, A s ≤ a s + 4 * h)
    (hsmall : h * Real.sqrt (T.card : ℝ) < η) :
    Real.sqrt (∑ s ∈ S, max (A s - a s) 0 ^ 2) < 4 * η := by
  have hcard : (S.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card hST
  have hle := (sqrt_sum_terminal_excess_sq_le S A a hh hA).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcard) (by positivity))
  have hlt : 4 * h * Real.sqrt (T.card : ℝ) < 4 * η := by nlinarith [hsmall]
  exact hle.trans_lt hlt

end CircleDomainRigidity.FiniteTransfer

end OAI
