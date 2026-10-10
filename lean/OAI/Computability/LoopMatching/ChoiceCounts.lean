import OAI.Computability.LoopMatching.LiteralChoices
import OAI.Computability.LoopMatching.ExpandInput
import Mathlib.Data.Fintype.Perm

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

noncomputable section
open scoped BigOperators
namespace LoopMatching

def ExpandedChoices (G : Input) (j : ℕ) : Type :=
  (N : (BinaryMatching.completeGraph (expand G j).n).Matching) ×
    ((e : N.val) → Fin (BinaryMatching.multiplicity (expand G j) e.val))

def AssignedChoices (G : Input) (j : ℕ) : Type :=
  (M : PartialMatching G.n) ×
    ((Fin j ≃ ↥(loopVertices M)) × MatchingChoices G M)

instance expandedChoicesFintype (G : Input) (j : ℕ) :
    Fintype (ExpandedChoices G j) := by
  classical
  unfold ExpandedChoices
  infer_instance

instance assignedChoicesFintype (G : Input) (j : ℕ) :
    Fintype (AssignedChoices G j) := by
  classical
  unfold AssignedChoices
  infer_instance

theorem card_expandedChoices (G : Input) (j : ℕ) :
    Fintype.card (ExpandedChoices G j) = BinaryMatching.count (expand G j) := by
  classical
  unfold ExpandedChoices BinaryMatching.count
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro N _
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_coe_sort]

theorem card_dummyAssignments {n : ℕ} (M : PartialMatching n) (j : ℕ) :
    Fintype.card (Fin j ≃ ↥(loopVertices M)) =
      if (loopVertices M).card = j then j.factorial else 0 := by
  classical
  by_cases h : (loopVertices M).card = j
  · rw [ite_eq_left h]
    let e : Fin j ≃ ↥(loopVertices M) := Fintype.equivOfCardEq (by
      simpa only [Fintype.card_fin, Fintype.card_coe] using h.symm)
    simpa only [Fintype.card_fin] using Fintype.card_equiv e
  · rw [ite_eq_right h]
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun e => h (by
      simpa only [Fintype.card_fin, Fintype.card_coe] using
        (Fintype.card_congr e).symm)⟩

theorem card_assignedChoices (G : Input) (j : ℕ) :
    Fintype.card (AssignedChoices G j) = j.factorial * countWithLoops G j := by
  classical
  unfold AssignedChoices
  rw [Fintype.card_sigma]
  unfold countWithLoops
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _
  rw [Fintype.card_prod, card_dummyAssignments, card_matchingChoices]
  by_cases h : (loopVertices M).card = j <;> simp [h]

theorem expanded_count_of_equiv (G : Input) (j : ℕ)
    (e : ExpandedChoices G j ≃ AssignedChoices G j) :
    BinaryMatching.count (expand G j) = j.factorial * countWithLoops G j := by
  rw [← card_expandedChoices, ← card_assignedChoices]
  exact Fintype.card_congr e

end LoopMatching

end

end OAI
