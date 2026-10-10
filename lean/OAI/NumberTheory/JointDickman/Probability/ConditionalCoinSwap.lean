import OAI.NumberTheory.JointDickman.Probability.ConditionalCoinAverage

namespace OAI

/-! # Exchanging the two sites in a conditional coin average -/

namespace JointDickman
open Finset

theorem conditionalCoinAverage_swap (P A D : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    conditionalCoinAverage P A D F =
      conditionalCoinAverage P D A (fun R Q I J U V => F Q R J I V U) := by
  unfold conditionalCoinAverage
  rw [sum_comm]
  conv_lhs => arg 2; ext J; arg 2; ext I; arg 2; ext Q; rw [sum_comm]
  conv_lhs => arg 2; ext J; arg 2; ext I; rw [sum_comm]
  conv_lhs => arg 2; ext J; arg 2; ext I; arg 2; ext R; arg 2; ext Q; rw [sum_comm]
  conv_lhs => arg 2; ext J; arg 2; ext I; arg 2; ext R; rw [sum_comm]
  apply sum_congr rfl
  intro J _
  apply sum_congr rfl
  intro I _
  apply sum_congr rfl
  intro R _
  apply sum_congr rfl
  intro U _
  apply sum_congr rfl
  intro Q _
  apply sum_congr rfl
  intro V _
  ring

end JointDickman

end OAI
