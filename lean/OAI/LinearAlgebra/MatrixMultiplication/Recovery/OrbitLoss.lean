import OAI.LinearAlgebra.MatrixMultiplication.Recovery.OrbitCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

namespace MatrixMultiplication.OrbitLoss

variable {X : Type*} [DecidableEq X]

theorem missing_card_partition (s : Finset X) (pass assigned : X → Prop)
    [DecidablePred pass] [DecidablePred assigned] :
    (s.filter fun x => ¬(pass x ∧ assigned x)).card =
      (s.filter fun x => ¬pass x).card +
      (s.filter fun x => pass x ∧ ¬assigned x).card := by
  classical
  have heq : (s.filter fun x => ¬(pass x ∧ assigned x)) =
      (s.filter fun x => ¬pass x) ∪ (s.filter fun x => pass x ∧ ¬assigned x) := by
    ext x
    by_cases hp : pass x <;> simp [hp]
  have hd : Disjoint (s.filter fun x => ¬pass x)
      (s.filter fun x => pass x ∧ ¬assigned x) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2.1
  rw [heq, Finset.card_union_of_disjoint hd]

theorem missing_fraction_partition (s : Finset X) (pass assigned : X → Prop)
    [DecidablePred pass] [DecidablePred assigned] :
    ((s.filter fun x => ¬(pass x ∧ assigned x)).card : ℝ) / s.card =
      ((s.filter fun x => ¬pass x).card : ℝ) / s.card +
      ((s.filter fun x => pass x ∧ ¬assigned x).card : ℝ) / s.card := by
  rw [missing_card_partition, Nat.cast_add, add_div]

theorem combined_inverse_linear (s : Finset X) (pass assigned : X → Prop)
    [DecidablePred pass] [DecidablePred assigned] (C : ℝ) (N : ℕ)
    (hmask : ((s.filter fun x => ¬pass x).card : ℝ) / s.card ≤ C / N)
    (hcollision : ((s.filter fun x => pass x ∧ ¬assigned x).card : ℝ) / s.card ≤ 1 / N) :
    ((s.filter fun x => ¬(pass x ∧ assigned x)).card : ℝ) / s.card ≤ (C + 1) / N := by
  rw [missing_fraction_partition, add_div]
  exact add_le_add hmask hcollision

end MatrixMultiplication.OrbitLoss

end OAI
