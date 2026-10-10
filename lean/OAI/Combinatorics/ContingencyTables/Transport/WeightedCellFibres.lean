import OAI.Combinatorics.ContingencyTables.Transport.BalancedCellFibres

namespace OAI

/-! # Exact weighted summation over one physical cell's fibres -/

namespace ContingencyTables.BalancedCellFibres

open scoped BigOperators Classical

variable {C : Type*} [Fintype C] [DecidableEq C]

theorem weighted_fibre_sum (M : C → ℕ) (F : (C×Bool → ℕ) → ℝ)
    (t : C) (g : Fin (M t+1) → ℝ) :
    (∑ k : Fin (M t+1),fibre M F t k*g k)=
      ∑ a : Profiles M,F (profile M a)*g (a t) := by
  unfold fibre
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

end ContingencyTables.BalancedCellFibres

end OAI
