import OAI.Combinatorics.ContingencyTables.Transport.RationalReindex
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-! # Finite binary words and their exact uniform experiment laws -/

namespace ContingencyTables.FairBits

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

def binaryWordEquiv (k : ℕ) : (Fin k → Bool) ≃ Fin (2 ^ k) :=
  (Equiv.piCongrRight (fun _ : Fin k => finTwoEquiv.symm)).trans finFunctionFinEquiv

def splitWordEquiv (k l : ℕ) : (Fin (k + l) → Bool) ≃ ((Fin k → Bool) × (Fin l → Bool)) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

def pairWordEquiv (k l : ℕ) : (Fin (k + l) → Bool) ≃ (Fin (2 ^ k) × Fin (2 ^ l)) :=
  (splitWordEquiv k l).trans (Equiv.prodCongr (binaryWordEquiv k) (binaryWordEquiv l))

variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]

theorem uniform_equiv (e : α ≃ β) :
    equivLaw e (uniformLaw (α := α)) = uniformLaw (α := β) := by
  apply RationalLaw.ext
  funext y
  change 1 / (Fintype.card α : ℚ) = 1 / (Fintype.card β : ℚ)
  rw [Fintype.card_congr e]

theorem uniform_product :
    productLaw (uniformLaw (α := α)) (uniformLaw (α := β)) = uniformLaw (α := α × β) := by
  apply RationalLaw.ext
  funext y
  change (1 / (Fintype.card α : ℚ)) * (1 / (Fintype.card β : ℚ)) = 1 / (Fintype.card (α × β) : ℚ)
  rw [Fintype.card_prod, Nat.cast_mul]
  ring

omit [Nonempty α] [Nonempty β] in
theorem map_equiv [DecidableEq β] {γ : Type*} [Fintype γ] [DecidableEq γ]
    (e : α ≃ β) (p : RationalLaw α) (f : β → γ) :
    mapLaw (equivLaw e p) f = mapLaw p (fun x => f (e x)) := by
  apply RationalLaw.ext
  funext z
  symm
  change (∑ x, if f (e x) = z then p.mass x else 0) =
    ∑ y, if f y = z then p.mass (e.symm y) else 0
  apply Fintype.sum_equiv e
  intro x
  simp

end

end ContingencyTables.FairBits

end OAI
