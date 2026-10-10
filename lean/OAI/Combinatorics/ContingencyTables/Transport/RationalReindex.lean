import OAI.Combinatorics.ContingencyTables.Transport.FirstSuccess

namespace OAI

/-! # Finite rational laws transported through bijections -/

namespace ContingencyTables.ResidualMixture

variable {α : Type*} [Fintype α]

@[ext] theorem RationalLaw.ext {p q : RationalLaw α} (h : p.mass = q.mass) : p = q := by
  cases p
  cases q
  cases h
  rfl

end ContingencyTables.ResidualMixture

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {α β : Type*} [Fintype α] [Fintype β]

def equivLaw (e : α ≃ β) (p : RationalLaw α) : RationalLaw β where
  mass := fun y => p.mass (e.symm y)
  nonnegative := fun y => p.nonnegative (e.symm y)
  total := by
    have h := Fintype.sum_equiv e p.mass (fun y => p.mass (e.symm y)) (fun x => by simp)
    rw [← h, p.total]

theorem variation_equiv (e : α ≃ β) (p q : RationalLaw α) :
    variation (equivLaw e p) (equivLaw e q) = variation p q := by
  unfold variation equivLaw
  congr 1
  symm
  apply Fintype.sum_equiv e
  intro x
  simp

end ContingencyTables.FirstSuccess

end OAI
