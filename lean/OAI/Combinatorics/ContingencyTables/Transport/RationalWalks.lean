import OAI.Combinatorics.ContingencyTables.Transport.RationalReindex
import OAI.Combinatorics.ContingencyTables.Transport.RejectionLaw

namespace OAI

/-! # Independent composition of finite rational transition experiments -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {α β : Type*} [Fintype α] [Fintype β]

def bindLaw (p : RationalLaw α) (K : α → RationalLaw β) : RationalLaw β where
  mass := fun y => ∑ x, p.mass x * (K x).mass y
  nonnegative := fun y => Finset.sum_nonneg fun x _ => mul_nonneg (p.nonnegative x) ((K x).nonnegative y)
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (K _).total, mul_one, p.total]

variable [DecidableEq α]

/-- Each transition uses a fresh independent finite experiment. -/
def walkLaw (K : α → RationalLaw α) (a : α) : ℕ → RationalLaw α
  | 0 => pointLaw a
  | n + 1 => bindLaw (walkLaw K a n) K

end ContingencyTables.FirstSuccess

end OAI
