import OAI.Computability.PerfectCompleteness.Decoding.ChildAssemblyProjection
import OAI.Computability.PerfectCompleteness.Foundations.MultiplicationFormInjectiveLemmas
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedPrefixComparison

namespace OAI

section

namespace PerfectCompleteness.ProjectedCutChoices

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

private theorem mixture_const {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) :
    μ.mixture (fun _ => ν) = ν := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∑ a, μ.weight a * ν.weight x) = ν.weight x
  rw [← Finset.sum_mul, μ.normalized, one_mul]

private theorem product_mixture {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (P : A × B → FiniteDistribution C) :
    (μ.product ν).mixture P = μ.mixture (fun a => ν.mixture (fun b => P (a, b))) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  simp only [FiniteDistribution.mixture,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

private theorem lifted_keep {branch : Nat → Nat} {n t : Nat}
    (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ChildBlockProjection.liftedLaw calls rows (fun s a => MixedSupport.Projection.keep (slots s a)) =
      FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows slots) := by
  unfold ChildBlockProjection.liftedLaw
  have hmap : (ChildBlockProjection.rawPullback calls rows
      (fun s a => MixedSupport.Projection.keep (slots s a)) :
      ChildBlockCardinality.Raw calls rows slots → ChildBlockCardinality.Raw calls rows slots) = id := by
    funext block
    apply Prod.ext
    · funext call
      apply Subtype.ext
      funext x
      rfl
    · funext node row
      apply Subtype.ext
      funext x
      rfl
  rw [hmap, FiniteDistribution.pushforward_id]

variable {branch : Nat → Nat} {n t : Nat}
  {Z : Fin (branch n) → Type*} [∀ child, Fintype (Z child)]
  (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
  (projected : (child : Fin (branch n)) → Z child → Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ child z s a, MixedSupport.Projection
    (childSlots slots child s a) (projected child z s a))

def childDomain (child : Fin (branch n)) (choice : Bool × Z child) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  if choice.1 then projected child choice.2 else childSlots slots child

def childProjection (child : Fin (branch n)) (choice : Bool × Z child) :
    ∀ s a, MixedSupport.Projection (childSlots slots child s a)
      (childDomain slots projected child choice s a) := by
  rcases choice with ⟨flag, z⟩
  cases flag with
  | false => exact fun s a => MixedSupport.Projection.keep (childSlots slots child s a)
  | true => exact projection child z

abbrev Choices := (child : Fin (branch n)) → Bool × Z child

def selectedSlots (choices : Choices (Z := Z)) :
    Slots branch (n + 1) → Fin t → MixedSupport.Slot :=
  fun (s : Fin (branch n) × Slots branch n) a =>
    childDomain slots projected s.1 (choices s.1) s.2 a

def selectedProjection (choices : Choices (Z := Z)) :
    ∀ s a, MixedSupport.Projection (slots s a) (selectedSlots slots projected choices s a) :=
  fun (s : Fin (branch n) × Slots branch n) a =>
    childProjection slots projected projection s.1 (choices s.1) s.2 a

def choicesLaw (choiceLaw : (child : Fin (branch n)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) : FiniteDistribution (Choices (Z := Z)) :=
  FiniteProduct.law (fun child =>
    (ProjectionPosterior.bernoulli β hβ hβ').product (choiceLaw child))

def childLaw (calls : Nat) (rows : Nat → Nat)
    (child : Fin (branch n)) (choice : Bool × Z child) :
    FiniteDistribution (ChildBlockCardinality.Raw calls rows (childSlots slots child)) :=
  ChildBlockProjection.liftedLaw calls rows (childProjection slots projected projection child choice)

theorem row_eq_mixture (calls : Nat) (rows : Nat → Nat)
    (choiceLaw : (child : Fin (branch n)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (child : Fin (branch n)) :
    SparseReplacement.row
      (fun child => FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows (childSlots slots child)))
      (ChildBlockProjection.replacementLaws calls rows (fun child => childSlots slots child)
        projected projection choiceLaw) β hβ hβ' child =
      ((ProjectionPosterior.bernoulli β hβ hβ').product (choiceLaw child)).mixture
        (childLaw slots projected projection calls rows child) := by
  rw [product_mixture]
  unfold SparseReplacement.row
  apply congrArg ((ProjectionPosterior.bernoulli β hβ hβ').mixture)
  funext flag
  cases flag with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      change FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows (childSlots slots child)) =
        (choiceLaw child).mixture (fun z => ChildBlockProjection.liftedLaw calls rows
          (fun s a => MixedSupport.Projection.keep (childSlots slots child s a)))
      simp only [lifted_keep, mixture_const]
  | true => rfl

theorem raw_eq_mixture (calls : Nat) (rows : Nat → Nat)
    (choiceLaw : (child : Fin (branch n)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    SparseReplacement.law
      (fun child => FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows (childSlots slots child)))
      (ChildBlockProjection.replacementLaws calls rows (fun child => childSlots slots child)
        projected projection choiceLaw) β hβ hβ' =
      (choicesLaw choiceLaw β hβ hβ').mixture (fun choices =>
        FiniteProduct.law (fun child => childLaw slots projected projection calls rows child (choices child))) := by
  unfold SparseReplacement.law
  have hrow := funext (row_eq_mixture slots projected projection calls rows choiceLaw β hβ hβ')
  rw [hrow]
  exact MarkedKernelProduct.law_mixture
    (fun child => (ProjectionPosterior.bernoulli β hβ hβ').product (choiceLaw child))
    (childLaw slots projected projection calls rows)

omit [(child : Fin (branch n)) → Fintype (Z child)] in
theorem fixed_assembly (calls : Nat) (rows : Nat → Nat) (choices : Choices (Z := Z)) :
    (FiniteProduct.law (fun child =>
      childLaw slots projected projection calls rows child (choices child))).pushforward
        (CutChildGrouping.assemble slots rows) =
      (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls)
        (selectedSlots slots projected choices) rows)).pushforward
          (ChildAssemblyProjection.assembledPullback rows
            (selectedProjection slots projected projection choices)) := by
  have hraw : (CutChildGrouping.rawLaw (C := Fin calls)
      (selectedSlots slots projected choices) rows).pushforward
        (ChildAssemblyProjection.rawPullback rows (selectedProjection slots projected projection choices)) =
      FiniteProduct.law (fun child =>
        childLaw slots projected projection calls rows child (choices child)) := by
    exact FiniteProduct.pushforward_map
      (fun child => FiniteDistribution.uniform (CutChildGrouping.Child (C := Fin calls)
        (selectedSlots slots projected choices) rows child))
      (fun child => ChildAssemblyProjection.childPullback rows
        (selectedProjection slots projected projection choices) child)
  rw [← hraw]
  exact ChildAssemblyProjection.uniform_projected_assembly rows
    (selectedProjection slots projected projection choices)

theorem assembled_eq_mixture (calls : Nat) (rows : Nat → Nat)
    (choiceLaw : (child : Fin (branch n)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ProjectedPrefixComparison.assembledLaw calls rows slots projected projection choiceLaw β hβ hβ' =
      (choicesLaw choiceLaw β hβ hβ').mixture (fun choices =>
        (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls)
          (selectedSlots slots projected choices) rows)).pushforward
            (ChildAssemblyProjection.assembledPullback rows
              (selectedProjection slots projected projection choices))) := by
  unfold ProjectedPrefixComparison.assembledLaw
  rw [raw_eq_mixture slots projected projection calls rows choiceLaw β hβ hβ',
    FiniteDistribution.pushforward_mixture]
  apply congrArg ((choicesLaw choiceLaw β hβ hβ').mixture)
  funext choices
  exact fixed_assembly slots projected projection calls rows choices

end
end PerfectCompleteness.ProjectedCutChoices

end

end OAI
