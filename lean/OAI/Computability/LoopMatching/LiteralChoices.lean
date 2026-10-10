import OAI.Computability.LoopMatching.Model
import Mathlib.Data.Fintype.BigOperators

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

noncomputable section
open scoped BigOperators
namespace LoopMatching

def OrdinaryChoices (G : Input) (M : PartialMatching G.n) : Type :=
  (e : M.val) → Fin (BinaryMatching.multiplicity G.ordinary e.val)

def LoopChoices (G : Input) (M : PartialMatching G.n) : Type :=
  (v : loopVertices M) → Fin (loopMultiplicity G v.val)

def MatchingChoices (G : Input) (M : PartialMatching G.n) : Type :=
  OrdinaryChoices G M × LoopChoices G M

def Choices (G : Input) : Type :=
  (M : PartialMatching G.n) × MatchingChoices G M

instance ordinaryChoicesFintype (G : Input) (M : PartialMatching G.n) :
    Fintype (OrdinaryChoices G M) := by
  classical
  unfold OrdinaryChoices
  infer_instance

instance loopChoicesFintype (G : Input) (M : PartialMatching G.n) :
    Fintype (LoopChoices G M) := by
  classical
  unfold LoopChoices
  infer_instance

instance matchingChoicesFintype (G : Input) (M : PartialMatching G.n) :
    Fintype (MatchingChoices G M) := by
  unfold MatchingChoices
  infer_instance

instance choicesFintype (G : Input) : Fintype (Choices G) := by
  unfold Choices
  infer_instance

theorem card_ordinaryChoices (G : Input) (M : PartialMatching G.n) :
    Fintype.card (OrdinaryChoices G M) =
      ∏ e ∈ M.val, BinaryMatching.multiplicity G.ordinary e := by
  classical
  unfold OrdinaryChoices
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_coe_sort]

theorem card_loopChoices (G : Input) (M : PartialMatching G.n) :
    Fintype.card (LoopChoices G M) =
      ∏ v ∈ loopVertices M, loopMultiplicity G v := by
  classical
  unfold LoopChoices
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_coe_sort]

theorem card_matchingChoices (G : Input) (M : PartialMatching G.n) :
    Fintype.card (MatchingChoices G M) = weight G M := by
  unfold MatchingChoices
  rw [Fintype.card_prod, card_ordinaryChoices, card_loopChoices]
  rfl

theorem count_eq_card_choices (G : Input) :
    count G = Fintype.card (Choices G) := by
  classical
  unfold Choices
  rw [Fintype.card_sigma]
  unfold count
  exact Finset.sum_congr rfl (fun M _ => (card_matchingChoices G M).symm)

end LoopMatching

end

end OAI
