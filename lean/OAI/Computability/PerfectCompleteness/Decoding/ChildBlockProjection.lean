import OAI.Computability.PerfectCompleteness.Algebra.UniformLinearImage
import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionOrderLemmas
import OAI.Computability.PerfectCompleteness.Foundations.MultiplicationFormInjectiveLemmas
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI


namespace PerfectCompleteness.ChildBlockProjection

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}

def nodeProjection
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (node : Nodes branch n) :
    ∀ s k, MixedSupport.Projection (nodeSlots slots node s k) (nodeSlots projected node s k) :=
  fun s k => p ((Nodes.path node).slotEmbedding s) k

theorem restrictNode_projection
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (node : Nodes branch n) (x : Domain slots) :
    sourceProjection (nodeProjection p node) (restrictNode slots node x) =
      restrictNode projected node (sourceProjection p x) := rfl

def squarePullback
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    squareSpace (H projected) →ₗ[F2] squareSpace (H slots) where
  toFun f := ⟨PointwiseSpaces.pullback F2 (sourceProjection p) f.val,
    TreeSourceSpaces.squareSpace_pullback_le p (Submodule.mem_map_of_mem f.property)⟩
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' c f := by apply Subtype.ext; rfl

@[simp] theorem squarePullback_apply
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (f : squareSpace (H projected)) (x : Domain slots) :
    (squarePullback p f).val x = f.val (sourceProjection p x) := rfl

theorem squarePullback_injective
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    Function.Injective (squarePullback p) := by
  intro f g h
  apply Subtype.ext
  exact PointwiseSpaces.pullback_injective (sourceProjection p) (sourceProjection_surjective p)
    (congrArg (fun z : squareSpace (H slots) => z.val) h)

def arraysPullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    Arrays projected rows →ₗ[F2] Arrays slots rows where
  toFun arrays node row := HPullback (nodeProjection p node) (arrays node row)
  map_add' a b := by
    funext node row
    exact map_add (HPullback (nodeProjection p node)) (a node row) (b node row)
  map_smul' c a := by
    funext node row
    exact map_smul (HPullback (nodeProjection p node)) c (a node row)

@[simp] theorem arraysPullback_apply (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (arrays : Arrays projected rows) (node : Nodes branch n)
    (row : Fin (rows (Nodes.height node))) :
    arraysPullback rows p arrays node row =
      HPullback (nodeProjection p node) (arrays node row) := rfl

theorem arraysPullback_injective (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    Function.Injective (arraysPullback rows p) := by
  intro a b h
  funext node row
  exact HPullback_injective (nodeProjection p node)
    (congrArg (fun z : Arrays slots rows => z node row) h)

theorem fullJoint_pullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (arrays : Arrays projected rows) (x : Domain slots) :
    fullJoint (arraysPullback rows p arrays) x = fullJoint arrays (sourceProjection p x) := rfl

def rawPullback (calls : Nat) (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    ChildBlockCardinality.Raw calls rows projected →ₗ[F2]
      ChildBlockCardinality.Raw calls rows slots where
  toFun block := (fun call => squarePullback p (block.1 call), arraysPullback rows p block.2)
  map_add' a b := by
    apply Prod.ext
    · funext call
      exact map_add (squarePullback p) (a.1 call) (b.1 call)
    · exact map_add (arraysPullback rows p) a.2 b.2
  map_smul' c a := by
    apply Prod.ext
    · funext call
      exact map_smul (squarePullback p) c (a.1 call)
    · exact map_smul (arraysPullback rows p) c a.2

theorem rawPullback_injective (calls : Nat) (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    Function.Injective (rawPullback calls rows p) := by
  intro a b h
  apply Prod.ext
  · funext call
    exact squarePullback_injective p
      (congrArg (fun z : ChildBlockCardinality.Raw calls rows slots => z.1 call) h)
  · exact arraysPullback_injective rows p
      (congrArg (fun z : ChildBlockCardinality.Raw calls rows slots => z.2) h)

def evaluate {calls : Nat} {rows : Nat → Nat}
    (block : ChildBlockCardinality.Raw calls rows slots) (x : Domain slots) :
    (Fin calls → F2) × Output branch n rows :=
  (fun call => (block.1 call).val x, fullJoint block.2 x)

theorem evaluate_pullback (calls : Nat) (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (block : ChildBlockCardinality.Raw calls rows projected) (x : Domain slots) :
    evaluate (rawPullback calls rows p block) x = evaluate block (sourceProjection p x) := rfl

def liftedLaw (calls : Nat) (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    FiniteDistribution (ChildBlockCardinality.Raw calls rows slots) :=
  (FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows projected)).pushforward
    (rawPullback calls rows p)

instance liftedRangeFintype (calls : Nat) (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    Fintype (LinearMap.range (rawPullback calls rows p)) := Fintype.ofFinite _

theorem liftedLaw_eq_uniform_range (calls : Nat) (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    liftedLaw calls rows p =
      (FiniteDistribution.uniform (LinearMap.range (rawPullback calls rows p))).pushforward
        (LinearMap.range (rawPullback calls rows p)).subtype := by
  rw [← UniformLinearImage.uniform_pushforward_linearMap
    (rawPullback calls rows p).rangeRestrict
    (rawPullback calls rows p).surjective_rangeRestrict]
  rw [FiniteDistribution.pushforward_comp]
  rfl

theorem liftedLaw_evaluate (calls : Nat) (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (x : Domain slots) :
    (liftedLaw calls rows p).pushforward (fun block => evaluate block x) =
      (FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows projected)).pushforward
        (fun block => evaluate block (sourceProjection p x)) := by
  rw [liftedLaw, FiniteDistribution.pushforward_comp]
  rfl

def mixtureLaw {Z : Type*} [Fintype Z] (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (projected : Z → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ z s k, MixedSupport.Projection (slots s k) (projected z s k))
    (choiceLaw : FiniteDistribution Z) :
    FiniteDistribution (ChildBlockCardinality.Raw calls rows slots) :=
  choiceLaw.mixture (fun z => liftedLaw calls rows (p z))

theorem mixtureLaw_weight {Z : Type*} [Fintype Z] (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (projected : Z → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ z s k, MixedSupport.Projection (slots s k) (projected z s k))
    (choiceLaw : FiniteDistribution Z) (block : ChildBlockCardinality.Raw calls rows slots) :
    (mixtureLaw calls rows slots projected p choiceLaw).weight block =
      ∑ z, choiceLaw.weight z * (liftedLaw calls rows (p z)).weight block := rfl


variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  {Z : I → Type*} [∀ i, Fintype (Z i)]

def replacementLaws (calls : Nat) (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (i : I) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s k, MixedSupport.Projection (slots i s k) (projected i z s k))
    (choiceLaw : (i : I) → FiniteDistribution (Z i)) :
    (i : I) → FiniteDistribution (ChildBlockCardinality.Raw calls rows (slots i)) :=
  fun i => mixtureLaw calls rows (slots i) (projected i) (p i) (choiceLaw i)

theorem observed_variation {Γ : Type*} [Fintype Γ]
    (calls : Nat) (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (i : I) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s k, MixedSupport.Projection (slots i s k) (projected i z s k))
    (choiceLaw : (i : I) → FiniteDistribution (Z i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (observe : ((i : I) → ChildBlockCardinality.Raw calls rows (slots i)) → Γ) :
    ((SparseReplacement.law
        (fun i => FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows (slots i)))
        (replacementLaws calls rows slots projected p choiceLaw) β hβ hβ').pushforward
          observe).totalVariation
      ((FiniteProduct.law (fun i =>
        FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows (slots i)))).pushforward
          observe) ≤
      Real.sqrt ((1 + β ^ 2 * ((ChildBlockCardinality.bound branch n t calls rows : ℝ) - 1)) ^
        Fintype.card I - 1) / 2 := by
  apply SparseReplacement.observed_uniform_variation
  intro i
  exact_mod_cast ChildBlockCardinality.fintype_card_le calls rows (slots i)

theorem adaptive_selection
    (calls : Nat) (rows : Nat → Nat)
    (slots : I → Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (i : I) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s k, MixedSupport.Projection (slots i s k) (projected i z s k))
    (choiceLaw : (i : I) → FiniteDistribution (Z i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (select : ((i : I) → ChildBlockCardinality.Raw calls rows (slots i)) → Finset I)
    (budget : Nat) (size : ∀ x, (select x).card ≤ budget) :
    (SparseReplacement.markedLaw
        (fun i => FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows (slots i)))
        (replacementLaws calls rows slots projected p choiceLaw) β hβ hβ'.le).probability
      (fun z => decide (∃ i ∈ select z.2, z.1 i = true)) ≤
        budget * (β * (ChildBlockCardinality.bound branch n t calls rows : ℝ) / (1 - β)) := by
  apply SparseReplacement.adaptive_uniform_selection _ β hβ hβ'
    (ChildBlockCardinality.bound branch n t calls rows : ℝ) ?_ select budget size
  intro i
  exact_mod_cast ChildBlockCardinality.fintype_card_le calls rows (slots i)

end
end PerfectCompleteness.ChildBlockProjection

end OAI
