import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

namespace OAI

/-! Cardinal bounds for pairwise disjoint nonempty branch sets. -/
namespace HadwigerMatching
open scoped BigOperators

variable {V : Type*} {t : ℕ}

/-- The number of one-vertex branches. -/
def singletonBranchCount (B : Fin t → Finset V) : ℕ :=
  (Finset.univ.filter fun i => (B i).card = 1).card

/-- The number of two-vertex branches. -/
def doubletonBranchCount (B : Fin t → Finset V) : ℕ :=
  (Finset.univ.filter fun i => (B i).card = 2).card

theorem sum_singleton_indicator (B : Fin t → Finset V) :
    (∑ i, if (B i).card = 1 then 1 else 0) = singletonBranchCount B := by
  simp [singletonBranchCount]

theorem sum_doubleton_indicator (B : Fin t → Finset V) :
    (∑ i, if (B i).card = 2 then 1 else 0) = doubletonBranchCount B := by
  simp [doubletonBranchCount]

/-- Disjoint branch sets occupy at most the ambient finite ground set. -/
theorem branch_card_sum_le [Fintype V] [DecidableEq V]
    (B : Fin t → Finset V) (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (∑ i, (B i).card) ≤ Fintype.card V := by
  have hd : (↑(Finset.univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint B :=
    fun i _ j _ hij => hdisj hij
  rw [← Finset.card_biUnion hd]
  exact Finset.card_le_univ _

/-- Every nonempty branch costs at least three, except for the exact deficits
of two for a singleton and one for a doubleton. -/
theorem branch_counting [Fintype V] [DecidableEq V]
    (B : Fin t → Finset V)
    (hne : ∀ i, (B i).Nonempty)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    3 * t ≤ Fintype.card V + 2 * singletonBranchCount B + doubletonBranchCount B := by
  have hpoint (i : Fin t) :
      3 ≤ (B i).card + 2 * (if (B i).card = 1 then 1 else 0) +
        (if (B i).card = 2 then 1 else 0) := by
    have hp : 0 < (B i).card := Finset.card_pos.mpr (hne i)
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  have hsum' : 3 * t ≤ (∑ i, (B i).card) +
      2 * singletonBranchCount B + doubletonBranchCount B := by
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_singleton_indicator, sum_doubleton_indicator, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_comm t 3] using hsum
  exact hsum'.trans (Nat.add_le_add_right
    (Nat.add_le_add_right (branch_card_sum_le B hdisj) _) _)

end HadwigerMatching

end OAI
