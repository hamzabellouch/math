import OAI.Computability.PerfectCompleteness.Foundations.ProjectedCutChoices
import OAI.Computability.PerfectCompleteness.Foundations.SlotProjectedExperiment

namespace OAI

section

namespace PerfectCompleteness.SourceProjectedChoices

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t m v : Nat}

abbrev Positions :=
  SourceQuestionPositionSplit.ChildPositions (branch := branch) (n := n) (t := t)

abbrev Choices :=
  ProjectedCutChoices.Choices (Z := fun _ : Fin (branch n) =>
    Positions (branch := branch) (n := n) (t := t))

def tagEquiv : Choices (branch := branch) (n := n) (t := t) ≃
    SourceProjectedTag.Tag (branch := branch) (n := n) (t := t) where
  toFun choices := (fun child => (choices child).2, fun child => (choices child).1)
  invFun tag child := (tag.2 child, tag.1 child)
  left_inv _ := rfl
  right_inv _ := rfl

def choiceLaw (_child : Fin (branch n)) :
    FiniteDistribution (Positions (branch := branch) (n := n) (t := t)) :=
  FiniteDistribution.uniform _

theorem tagEquiv_law (flag : Fin (branch n) → FiniteDistribution Bool) :
    (FiniteProduct.law (fun child =>
      (flag child).product (choiceLaw (t := t) child))).pushforward
        (tagEquiv (branch := branch) (n := n) (t := t)) =
      SourceProjectedTag.law (t := t) flag := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro tag
  change (∏ child : Fin (branch n), (flag child).weight (tag.2 child) *
      (choiceLaw (t := t) child).weight (tag.1 child)) =
    (∏ child : Fin (branch n), (choiceLaw (t := t) child).weight (tag.1 child)) *
      ∏ child : Fin (branch n), (flag child).weight (tag.2 child)
  rw [Finset.prod_mul_distrib, mul_comm]

theorem choicesLaw_tagEquiv (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (ProjectedCutChoices.choicesLaw
      (choiceLaw (branch := branch) (n := n) (t := t)) β hβ hβ').pushforward
        (tagEquiv (branch := branch) (n := n) (t := t)) =
      SourceProjectedTag.law (t := t)
        (fun _ : Fin (branch n) => ProjectionPosterior.bernoulli β hβ hβ') :=
  tagEquiv_law (t := t) (fun _ => ProjectionPosterior.bernoulli β hβ hβ')

theorem tagLaw_choices (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (SourceProjectedTag.law (t := t)
      (fun _ : Fin (branch n) => ProjectionPosterior.bernoulli β hβ hβ')).pushforward
        (tagEquiv (branch := branch) (n := n) (t := t)).symm =
      ProjectedCutChoices.choicesLaw
        (choiceLaw (branch := branch) (n := n) (t := t)) β hβ hβ' := by
  rw [← choicesLaw_tagEquiv β hβ hβ', FiniteDistribution.pushforward_comp]
  simp only [Equiv.symm_apply_apply]
  exact FiniteDistribution.pushforward_id _

variable (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)

def projected (child : Fin (branch n))
    (positions : Positions (branch := branch) (n := n) (t := t)) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  fun leaf a => SlotProjectedExperiment.selectSlot (slots (child, leaf) a) (positions leaf a)

def projection : ∀ child positions leaf a,
    MixedSupport.Projection (childSlots slots child leaf a)
      (projected slots child positions leaf a) :=
  fun child positions leaf a =>
    SlotProjectedExperiment.selectProjection (slots (child, leaf) a) (positions leaf a)

theorem childDomain_eq (child : Fin (branch n)) (flag : Bool)
    (positions : Positions (branch := branch) (n := n) (t := t))
    (leaf : Slots branch n) (a : Fin t) :
    ProjectedCutChoices.childDomain slots (projected slots) child (flag, positions) leaf a =
      SlotProjectedExperiment.flaggedSlot (slots (child, leaf) a) (positions leaf a) flag := by
  cases flag <;> rfl

theorem childProjection_heq (child : Fin (branch n)) (flag : Bool)
    (positions : Positions (branch := branch) (n := n) (t := t))
    (leaf : Slots branch n) (a : Fin t) :
    HEq (ProjectedCutChoices.childProjection slots (projected slots) (projection slots)
      child (flag, positions) leaf a)
      (SlotProjectedExperiment.flaggedProjection
        (slots (child, leaf) a) (positions leaf a) flag) := by
  cases flag <;> rfl

theorem selectedSlots_tag
    (tag : SourceProjectedTag.Tag (branch := branch) (n := n) (t := t)) :
    ProjectedCutChoices.selectedSlots slots (projected slots) (tagEquiv.symm tag) =
      SlotProjectedExperiment.mixedInside slots tag.1 tag.2 := by
  funext leaf a
  exact childDomain_eq slots leaf.1 (tag.2 leaf.1) (tag.1 leaf.1) leaf.2 a

private theorem projection_family_heq
    {left right₁ right₂ : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (hr : right₁ = right₂)
    (p₁ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₁ leaf a))
    (p₂ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₂ leaf a))
    (hp : ∀ leaf a, HEq (p₁ leaf a) (p₂ leaf a)) : HEq p₁ p₂ := by
  subst right₂
  apply heq_of_eq
  funext leaf a
  exact eq_of_heq (hp leaf a)

theorem selectedProjection_tag
    (tag : SourceProjectedTag.Tag (branch := branch) (n := n) (t := t)) :
    HEq (ProjectedCutChoices.selectedProjection slots (projected slots) (projection slots)
      (tagEquiv.symm tag))
      (SlotProjectedExperiment.insideProjection slots tag.1 tag.2) := by
  apply projection_family_heq (selectedSlots_tag slots tag)
  intro leaf a
  exact childProjection_heq slots leaf.1 (tag.2 leaf.1) (tag.1 leaf.1) leaf.2 a

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)
  (questions : SourceQuestionPositionSplit.Questions
    (branch := branch) (n := n) (t := t) (m := m))

theorem selectedSlots_source
    (tag : SourceProjectedTag.Tag (branch := branch) (n := n) (t := t)) :
    ProjectedCutChoices.selectedSlots (SourceProjectedTag.originalSlots clauses questions)
      (projected (SourceProjectedTag.originalSlots clauses questions)) (tagEquiv.symm tag) =
      SourceProjectedTag.mixedInside clauses designated questions tag.1 tag.2 :=
  (selectedSlots_tag (SourceProjectedTag.originalSlots clauses questions) tag).trans
    (SlotProjectedExperiment.mixedInside_source clauses designated questions tag.1 tag.2)

theorem selectedProjection_source
    (tag : SourceProjectedTag.Tag (branch := branch) (n := n) (t := t)) :
    HEq (ProjectedCutChoices.selectedProjection
      (SourceProjectedTag.originalSlots clauses questions)
      (projected (SourceProjectedTag.originalSlots clauses questions))
      (projection (SourceProjectedTag.originalSlots clauses questions)) (tagEquiv.symm tag))
      (SourceProjectedTag.projection clauses designated questions tag.1 tag.2) :=
  (selectedProjection_tag (SourceProjectedTag.originalSlots clauses questions) tag).trans
    (SlotProjectedExperiment.insideProjection_source clauses designated questions tag.1 tag.2)

end
end PerfectCompleteness.SourceProjectedChoices

end

end OAI
