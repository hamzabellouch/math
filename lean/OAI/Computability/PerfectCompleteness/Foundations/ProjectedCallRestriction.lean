import OAI.Computability.PerfectCompleteness.Foundations.ProjectedPrefixComparison
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas

namespace OAI

section

namespace PerfectCompleteness.ProjectedCallRestriction

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t oldCalls enlargedCalls : Nat}

def rawRestrict (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (e : Fin oldCalls → Fin enlargedCalls) :
    ChildBlockCardinality.Raw enlargedCalls rows slots →ₗ[F2]
      ChildBlockCardinality.Raw oldCalls rows slots where
  toFun block := (fun call => block.1 (e call), block.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem rawRestrict_calls (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (e : Fin oldCalls → Fin enlargedCalls)
    (block : ChildBlockCardinality.Raw enlargedCalls rows slots) (call : Fin oldCalls) :
    (rawRestrict rows slots e block).1 call = block.1 (e call) := rfl

@[simp] theorem rawRestrict_arrays (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (e : Fin oldCalls → Fin enlargedCalls)
    (block : ChildBlockCardinality.Raw enlargedCalls rows slots) :
    (rawRestrict rows slots e block).2 = block.2 := rfl

theorem rawRestrict_surjective (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (e : Fin oldCalls → Fin enlargedCalls) (he : Function.Injective e) :
    Function.Surjective (rawRestrict rows slots e) := by
  rintro ⟨calls, arrays⟩
  refine ⟨(Function.extend e calls (fun _ => 0), arrays), ?_⟩
  apply Prod.ext
  · funext call
    exact he.extend_apply calls (fun _ => 0) call
  · rfl

theorem uniform_restrict_law (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (e : Fin oldCalls → Fin enlargedCalls) (he : Function.Injective e) :
    (FiniteDistribution.uniform (ChildBlockCardinality.Raw enlargedCalls rows slots)).pushforward
        (rawRestrict rows slots e) =
      FiniteDistribution.uniform (ChildBlockCardinality.Raw oldCalls rows slots) :=
  UniformLinearImage.uniform_pushforward_linearMap
    (rawRestrict rows slots e) (rawRestrict_surjective rows slots e he)

theorem rawRestrict_pullback (rows : Nat → Nat)
    {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (e : Fin oldCalls → Fin enlargedCalls)
    (block : ChildBlockCardinality.Raw enlargedCalls rows projected) :
    rawRestrict rows slots e (ChildBlockProjection.rawPullback enlargedCalls rows p block) =
      ChildBlockProjection.rawPullback oldCalls rows p (rawRestrict rows projected e block) := rfl

theorem lifted_restrict_law (rows : Nat → Nat)
    {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (e : Fin oldCalls → Fin enlargedCalls) (he : Function.Injective e) :
    (ChildBlockProjection.liftedLaw enlargedCalls rows p).pushforward (rawRestrict rows slots e) =
      ChildBlockProjection.liftedLaw oldCalls rows p := by
  unfold ChildBlockProjection.liftedLaw
  rw [FiniteDistribution.pushforward_comp]
  change (FiniteDistribution.uniform (ChildBlockCardinality.Raw enlargedCalls rows projected)).pushforward
    (fun block => ChildBlockProjection.rawPullback oldCalls rows p
      (rawRestrict rows projected e block)) = _
  rw [← FiniteDistribution.pushforward_comp
    (FiniteDistribution.uniform (ChildBlockCardinality.Raw enlargedCalls rows projected))
    (rawRestrict rows projected e) (ChildBlockProjection.rawPullback oldCalls rows p),
    uniform_restrict_law rows projected e he]

theorem mixture_restrict_law {Z : Type*} [Fintype Z] (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (projected : Z → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ z s k, MixedSupport.Projection (slots s k) (projected z s k))
    (choiceLaw : FiniteDistribution Z)
    (e : Fin oldCalls → Fin enlargedCalls) (he : Function.Injective e) :
    (ChildBlockProjection.mixtureLaw enlargedCalls rows slots projected p choiceLaw).pushforward
        (rawRestrict rows slots e) =
      ChildBlockProjection.mixtureLaw oldCalls rows slots projected p choiceLaw := by
  unfold ChildBlockProjection.mixtureLaw
  rw [FiniteDistribution.pushforward_mixture]
  apply congrArg choiceLaw.mixture
  funext z
  exact lifted_restrict_law rows (p z) e he

private theorem sparse_pushforward {I : Type*} [Fintype I] [DecidableEq I]
    {Ω Γ : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (Γ i)]
    (P Q : (i : I) → FiniteDistribution (Ω i))
    (f : (i : I) → Ω i → Γ i) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (SparseReplacement.law P Q β hβ hβ').pushforward (fun x i => f i (x i)) =
      SparseReplacement.law (fun i => (P i).pushforward (f i))
        (fun i => (Q i).pushforward (f i)) β hβ hβ' := by
  unfold SparseReplacement.law
  rw [FiniteProduct.pushforward_map (SparseReplacement.row P Q β hβ hβ') f]
  apply congrArg (fun laws : (i : I) → FiniteDistribution (Γ i) => FiniteProduct.law laws)
  funext i
  unfold SparseReplacement.row
  rw [FiniteDistribution.pushforward_mixture]
  apply congrArg ((ProjectionPosterior.bernoulli β hβ hβ').mixture)
  funext marked
  cases marked <;> rfl

def restrictChildren {I : Type*} (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (e : Fin oldCalls → Fin enlargedCalls)
    (blocks : (i : I) → ChildBlockCardinality.Raw enlargedCalls rows (slots i)) :
    (i : I) → ChildBlockCardinality.Raw oldCalls rows (slots i) :=
  fun i => rawRestrict rows (slots i) e (blocks i)

theorem sparse_restrict_law {I : Type*} [Fintype I] [DecidableEq I]
    {Z : I → Type*} [∀ i, Fintype (Z i)]
    (rows : Nat → Nat) (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (i : I) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s k, MixedSupport.Projection (slots i s k) (projected i z s k))
    (choiceLaw : (i : I) → FiniteDistribution (Z i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (e : Fin oldCalls → Fin enlargedCalls) (he : Function.Injective e) :
    (SparseReplacement.law
      (fun i => FiniteDistribution.uniform (ChildBlockCardinality.Raw enlargedCalls rows (slots i)))
      (ChildBlockProjection.replacementLaws enlargedCalls rows slots projected p choiceLaw)
      β hβ hβ').pushforward (restrictChildren rows slots e) =
      SparseReplacement.law
        (fun i => FiniteDistribution.uniform (ChildBlockCardinality.Raw oldCalls rows (slots i)))
        (ChildBlockProjection.replacementLaws oldCalls rows slots projected p choiceLaw)
        β hβ hβ' := by
  unfold restrictChildren
  rw [sparse_pushforward
    (fun i => FiniteDistribution.uniform (ChildBlockCardinality.Raw enlargedCalls rows (slots i)))
    (ChildBlockProjection.replacementLaws enlargedCalls rows slots projected p choiceLaw)
    (fun i => ⇑(rawRestrict rows (slots i) e)) β hβ hβ']
  apply congrArg₂ (fun (P Q : (i : I) →
    FiniteDistribution (ChildBlockCardinality.Raw oldCalls rows (slots i))) =>
      SparseReplacement.law P Q β hβ hβ')
  · funext i
    exact uniform_restrict_law rows (slots i) e he
  · funext i
    exact mixture_restrict_law rows (slots i) (projected i) (p i) (choiceLaw i) e he

def assembledRestrict (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (e : Fin oldCalls → Fin enlargedCalls) :
    CutChildGrouping.Assembled (C := Fin enlargedCalls) slots rows →ₗ[F2]
      CutChildGrouping.Assembled (C := Fin oldCalls) slots rows where
  toFun record := (fun call => record.1 (e call), record.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem assembledRestrict_calls (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (e : Fin oldCalls → Fin enlargedCalls)
    (record : CutChildGrouping.Assembled (C := Fin enlargedCalls) slots rows)
    (call : Fin oldCalls) :
    (assembledRestrict rows slots e record).1 call = record.1 (e call) := rfl

@[simp] theorem assembledRestrict_arrays (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (e : Fin oldCalls → Fin enlargedCalls)
    (record : CutChildGrouping.Assembled (C := Fin enlargedCalls) slots rows) :
    (assembledRestrict rows slots e record).2 = record.2 := rfl

theorem assemble_restrict (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (e : Fin oldCalls → Fin enlargedCalls)
    (blocks : CutChildGrouping.Raw (C := Fin enlargedCalls) slots rows) :
    assembledRestrict rows slots e (CutChildGrouping.assemble slots rows blocks) =
      CutChildGrouping.assemble slots rows
        (restrictChildren rows (fun i => childSlots slots i) e blocks) := rfl

theorem assembled_restrict_law
    {Z : Fin (branch n) → Type*} [∀ i, Fintype (Z i)]
    (rows : Nat → Nat) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (projected : (i : Fin (branch n)) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s k, MixedSupport.Projection (childSlots slots i s k) (projected i z s k))
    (choiceLaw : (i : Fin (branch n)) → FiniteDistribution (Z i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (e : Fin oldCalls → Fin enlargedCalls) (he : Function.Injective e) :
    (ProjectedPrefixComparison.assembledLaw enlargedCalls rows slots projected p choiceLaw β hβ hβ').pushforward
        (assembledRestrict rows slots e) =
      ProjectedPrefixComparison.assembledLaw oldCalls rows slots projected p choiceLaw β hβ hβ' := by
  unfold ProjectedPrefixComparison.assembledLaw
  rw [FiniteDistribution.pushforward_comp]
  have hmap :
      (fun blocks : CutChildGrouping.Raw (C := Fin enlargedCalls) slots rows =>
        assembledRestrict rows slots e (CutChildGrouping.assemble slots rows blocks)) =
      (fun blocks => CutChildGrouping.assemble slots rows
        (restrictChildren rows (fun i => childSlots slots i) e blocks)) := rfl
  rw [hmap, ← FiniteDistribution.pushforward_comp
    (SparseReplacement.law
      (fun i => FiniteDistribution.uniform (ChildBlockCardinality.Raw enlargedCalls rows (childSlots slots i)))
      (ChildBlockProjection.replacementLaws enlargedCalls rows (fun i => childSlots slots i)
        projected p choiceLaw) β hβ hβ')
    (restrictChildren rows (fun i => childSlots slots i) e)
    (CutChildGrouping.assemble (C := Fin oldCalls) slots rows),
    sparse_restrict_law rows (fun i => childSlots slots i) projected p choiceLaw β hβ hβ' e he]

end
end PerfectCompleteness.ProjectedCallRestriction

end

end OAI
