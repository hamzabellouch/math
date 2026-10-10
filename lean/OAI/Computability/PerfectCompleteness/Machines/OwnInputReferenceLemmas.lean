import OAI.Computability.PerfectCompleteness.Algebra.TensorBucketEvaluationLemmas
import OAI.Computability.PerfectCompleteness.Construction.HiddenBucketBias
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalArrays
import OAI.Computability.PerfectCompleteness.Foundations.QuotientTableAgreementLemmas
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaceEquivLemmas

namespace OAI


namespace PerfectCompleteness.OwnInputReference

open scoped BigOperators TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

abbrev UpperSpace := H (nodeSlots slots upper)
abbrev UpperVector := Block rows upper
abbrev LowerVector := Block rows lower
abbrev OtherNodes := {node : Nodes branch n // node ≠ upper ∧ node ≠ lower}

structure Cut where
  proper : Nodes.height lower < Nodes.height upper
  path : DescendantSpaces.Path branch (Nodes.height upper) (Nodes.height lower)
  slots_agree : ∀ s,
    (Nodes.path upper).slotEmbedding (path.slotEmbedding s) =
      (Nodes.path lower).slotEmbedding s

theorem Cut.upper_ne_lower (cut : Cut upper lower) : upper ≠ lower := by
  intro h
  have hlt := cut.proper
  rw [h] at hlt
  exact (Nat.lt_irrefl _) hlt

theorem Cut.family_eq (cut : Cut upper lower) :
    cut.path.family (LeafDomain (nodeSlots slots upper)) = LeafDomain (nodeSlots slots lower) := by
  funext s
  change ((k : Fin t) →
      (slots ((Nodes.path upper).slotEmbedding (cut.path.slotEmbedding s)) k).Domain) =
    ((k : Fin t) → (slots ((Nodes.path lower).slotEmbedding s) k).Domain)
  rw [cut.slots_agree]

abbrev OtherArrays :=
  (node : OtherNodes upper lower) →
    Fin (rows (Nodes.height node.1)) → H (nodeSlots slots node.1)

structure Exterior where
  otherArrays : OtherArrays slots rows upper lower
  lowerRows : Fin (rows (Nodes.height lower)) → H (nodeSlots slots lower)

instance exteriorFinite : Finite (Exterior slots rows upper lower) := by
  let f : Exterior slots rows upper lower →
      OtherArrays slots rows upper lower ×
        (Fin (rows (Nodes.height lower)) → H (nodeSlots slots lower)) :=
    fun x => (x.otherArrays, x.lowerRows)
  exact Finite.of_injective f (by intro x y h; cases x; cases y; cases h; rfl)

instance exteriorFintype : Fintype (Exterior slots rows upper lower) := Fintype.ofFinite _

variable (W : Submodule F2 (UpperVector rows upper)) (a : LowerVector rows lower)

structure Input where
  knownBuckets : HiddenBucketBias.VisibleDirection W → UpperSpace slots upper
  otherArrays : OtherArrays slots rows upper lower
  lowerQuotient : Domain (nodeSlots slots lower) → DirectionQuotient.Space a

def readInput {Ω : Type*} (eval : Ω → UpperSpace slots upper)
    (data : HiddenBucketBias.VisibleTape W Ω × Exterior slots rows upper lower) :
    Input slots rows upper lower W a where
  knownBuckets v := eval (data.1 v)
  otherArrays := data.2.otherArrays
  lowerQuotient x := DirectionQuotient.proj a
    (fun i => (data.2.lowerRows i).val x)

abbrev SideOutput := DirectionQuotient.Space a ×
  ((node : OtherNodes upper lower) → Block rows node.1)

def sideFunction (input : Input slots rows upper lower W a) :
    Domain slots → SideOutput rows upper lower a :=
  fun x =>
    (input.lowerQuotient (restrictNode slots lower x),
      fun node row => (input.otherArrays node row).val (restrictNode slots node.1 x))

def knownOutput (input : Input slots rows upper lower W a)
    (x : Domain (nodeSlots slots upper)) : UpperVector rows upper :=
  ∑ v : HiddenBucketBias.VisibleDirection W,
    (input.knownBuckets v).val x • v.val.val

def query (input : Input slots rows upper lower W a)
    (X : W ⊗[F2] UpperSpace slots upper) :
    Domain slots → UpperVector rows upper × SideOutput rows upper lower a :=
  fun x =>
    (knownOutput slots rows upper lower W a input (restrictNode slots upper x) +
      TensorBucketEvaluation.tensorOutput W
        (EvaluationMatrix.evaluation (UpperSpace slots upper) (restrictNode slots upper x)) X,
     sideFunction slots rows upper lower W a input x)

def sampledQuery {Ω : Type*} (eval : Ω → UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : Exterior slots rows upper lower) :
    Domain slots → UpperVector rows upper × SideOutput rows upper lower a :=
  fun x =>
    ((fun i => (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape i).val
        (restrictNode slots upper x)),
     (DirectionQuotient.proj a
        (fun i => (external.lowerRows i).val (restrictNode slots lower x)),
      fun node row => (external.otherArrays node row).val (restrictNode slots node.1 x)))

theorem query_readInput_hidden {Ω : Type*} (eval : Ω → UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : Exterior slots rows upper lower) :
    query slots rows upper lower W a
      (readInput slots rows upper lower W a eval
        ((HiddenBucketBias.splitTape W Ω tape).2, external))
      (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω tape).1) =
      sampledQuery slots rows upper lower a eval tape external := by
  funext x
  apply Prod.ext
  · exact (TensorBucketEvaluation.evaluate_apply_split W (UpperSpace slots upper)
      eval tape (restrictNode slots upper x)).symm
  · rfl

def response (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (input : Input slots rows upper lower W a)
    (X : W ⊗[F2] UpperSpace slots upper) : UpperVector rows upper :=
  (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
    (TreeCanonical.numberedFunction slots (query slots rows upper lower W a input X))).1

theorem response_readInput_hidden {Ω : Type*}
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (eval : Ω → UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : Exterior slots rows upper lower) :
    response slots rows upper lower W a labeling
      (readInput slots rows upper lower W a eval
        ((HiddenBucketBias.splitTape W Ω tape).2, external))
      (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω tape).1) =
      (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
        (TreeCanonical.numberedFunction slots
          (sampledQuery slots rows upper lower a eval tape external))).1 := by
  unfold response
  rw [query_readInput_hidden]

def referenceLaw (repeats : Nat → Nat) (cut : Cut upper lower) :
    FiniteDistribution (W ⊗[F2] UpperSpace slots upper) :=
  HiddenBucketBias.recursiveLaw W repeats cut.path (LeafDomain (nodeSlots slots upper))

abbrev ScalarSample (repeats : Nat → Nat) (cut : Cut upper lower) :=
  RecursiveSampler.Tape F2 repeats cut.path (LeafDomain (nodeSlots slots upper))

instance scalarSampleFintype (repeats : Nat → Nat) (cut : Cut upper lower) :
    Fintype (ScalarSample slots upper lower repeats cut) := by
  change Fintype ((j : RecursiveSampler.DrawIndex repeats cut.path) →
    RecursiveSampler.DrawSpace F2 repeats cut.path (LeafDomain (nodeSlots slots upper)) j)
  infer_instance

abbrev RawSample (repeats : Nat → Nat) (cut : Cut upper lower) :=
  HiddenBucketBias.HiddenTape W (ScalarSample slots upper lower repeats cut) ×
    (HiddenBucketBias.VisibleTape W (ScalarSample slots upper lower repeats cut) ×
      Exterior slots rows upper lower)

instance rawSampleFintype (repeats : Nat → Nat) (cut : Cut upper lower) :
    Fintype (RawSample slots rows upper lower W repeats cut) := by
  change Fintype
    ((HiddenBucketBias.HiddenDirection W → ScalarSample slots upper lower repeats cut) ×
      ((HiddenBucketBias.VisibleDirection W → ScalarSample slots upper lower repeats cut) ×
        Exterior slots rows upper lower))
  infer_instance

def rawLaw (repeats : Nat → Nat) (cut : Cut upper lower)
    (externalLaw : FiniteDistribution (Exterior slots rows upper lower)) :
    FiniteDistribution (RawSample slots rows upper lower W repeats cut) :=
  HiddenBucketBias.exposedLaw W
    (RecursiveSampler.tapeLaw F2 repeats cut.path (LeafDomain (nodeSlots slots upper))) externalLaw

def inputEvent (repeats : Nat → Nat) (cut : Cut upper lower)
    (observed : Input slots rows upper lower W a) :
    RawSample slots rows upper lower W repeats cut → Bool :=
  fun x => decide (readInput slots rows upper lower W a
    (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper)))
      x.2 = observed)

theorem conditional_referenceLaw (repeats : Nat → Nat) (cut : Cut upper lower)
    (externalLaw : FiniteDistribution (Exterior slots rows upper lower))
    (observed : Input slots rows upper lower W a)
    (positive : 0 < (rawLaw slots rows upper lower W repeats cut externalLaw).probability
      (inputEvent slots rows upper lower W a repeats cut observed)) :
    ((rawLaw slots rows upper lower W repeats cut externalLaw).condition
      (inputEvent slots rows upper lower W a repeats cut observed) positive).pushforward
      (fun x => HiddenBucketBias.hiddenSum W
        (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper))) x.1) =
      referenceLaw slots rows upper lower W repeats cut := by
  exact HiddenBucketBias.law_condition_exterior W
    (RecursiveSampler.tapeLaw F2 repeats cut.path (LeafDomain (nodeSlots slots upper)))
    externalLaw
    (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper)))
    (fun x => decide (readInput slots rows upper lower W a
      (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper))) x = observed))
    positive

instance frequencyFintype : Fintype (Module.Dual F2 (W ⊗[F2] UpperSpace slots upper)) :=
  Fintype.ofInjective
    (fun f : Module.Dual F2 (W ⊗[F2] UpperSpace slots upper) =>
      (f : (W ⊗[F2] UpperSpace slots upper) → F2)) DFunLike.coe_injective

def heavyList (repeats : Nat → Nat) (cut : Cut upper lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (input : Input slots rows upper lower W a)
    (σ : Module.Dual F2 (UpperVector rows upper)) (threshold : ℝ) :
    Finset (Module.Dual F2 (W ⊗[F2] UpperSpace slots upper)) :=
  SmallBias.heavySet (referenceLaw slots rows upper lower W repeats cut)
    (fun Φ X => QuarterBalance.sign (Φ X))
    (fun X => QuarterBalance.sign (σ (response slots rows upper lower W a labeling input X)))
    threshold

theorem mem_heavyList (repeats : Nat → Nat) (cut : Cut upper lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (input : Input slots rows upper lower W a)
    (σ : Module.Dual F2 (UpperVector rows upper)) (threshold : ℝ)
    (Φ : Module.Dual F2 (W ⊗[F2] UpperSpace slots upper)) :
    Φ ∈ heavyList slots rows upper lower W a repeats cut labeling input σ threshold ↔
      threshold ≤ |(referenceLaw slots rows upper lower W repeats cut).expectation
        (fun X => QuarterBalance.sign (σ (response slots rows upper lower W a labeling input X)) *
          QuarterBalance.sign (Φ X))| := by
  simp only [heavyList, SmallBias.heavySet, Finset.mem_filter, Finset.mem_univ, true_and]

end
end PerfectCompleteness.OwnInputReference



namespace PerfectCompleteness.OwnInputCanonicalQuery

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

abbrev CanonicalOutput (a : Block rows lower) :=
  DirectionQuotient.Space a ×
    (BlockQuotient.OtherBlocks (fun node : Nodes branch n => Block rows node) lower × PUnit.{1})

def reorder (hne : upper ≠ lower) (a : Block rows lower) :
    CanonicalOutput rows lower a →
      OwnInputReference.UpperVector rows upper × OwnInputReference.SideOutput rows upper lower a :=
  fun x => (x.2.1 ⟨upper, hne⟩,
    (x.1, fun node => x.2.1 ⟨node.val, node.property.2⟩))

theorem reorder_injective (hne : upper ≠ lower) (a : Block rows lower) :
    Function.Injective (reorder rows upper lower hne a) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun z => z.2.1) h
  · apply Prod.ext
    · funext node
      rcases node with ⟨node, hn⟩
      by_cases hu : node = upper
      · subst node
        exact congrArg Prod.fst h
      · exact congrFun (congrArg (fun z => z.2.2) h) ⟨node, hu, hn⟩
    · exact Subsingleton.elim _ _

def unreorder (a : Block rows lower) :
    OwnInputReference.UpperVector rows upper × OwnInputReference.SideOutput rows upper lower a →
      CanonicalOutput rows lower a :=
  fun y => (y.2.1,
    ((fun node => if h : node.val = upper then h.symm ▸ y.1
      else y.2.2 ⟨node.val, h, node.property⟩), PUnit.unit))

theorem reorder_unreorder (hne : upper ≠ lower) (a : Block rows lower)
    (y : OwnInputReference.UpperVector rows upper ×
      OwnInputReference.SideOutput rows upper lower a) :
    reorder rows upper lower hne a (unreorder rows upper lower a y) = y := by
  apply Prod.ext
  · simp [reorder, unreorder]
  · apply Prod.ext
    · rfl
    · funext node
      simp only [reorder, unreorder, dite_eq_right node.property.1]

def outputEquiv (hne : upper ≠ lower) (a : Block rows lower) :
    CanonicalOutput rows lower a ≃
      OwnInputReference.UpperVector rows upper × OwnInputReference.SideOutput rows upper lower a where
  toFun := reorder rows upper lower hne a
  invFun := unreorder rows upper lower a
  left_inv _ := reorder_injective rows upper lower hne a (reorder_unreorder rows upper lower hne a _)
  right_inv := reorder_unreorder rows upper lower hne a

def exteriorOf (arrays : Arrays slots rows) : OwnInputReference.Exterior slots rows upper lower where
  otherArrays node := arrays node.val
  lowerRows := arrays lower

def assemble (upperRows : Fin (rows (Nodes.height upper)) → H (nodeSlots slots upper))
    (external : OwnInputReference.Exterior slots rows upper lower) : Arrays slots rows :=
  fun node => if hu : node = upper then hu.symm ▸ upperRows
    else if hl : node = lower then hl.symm ▸ external.lowerRows
    else external.otherArrays ⟨node, hu, hl⟩

@[simp] theorem assemble_upper
    (upperRows : Fin (rows (Nodes.height upper)) → H (nodeSlots slots upper))
    (external : OwnInputReference.Exterior slots rows upper lower) :
    assemble slots rows upper lower upperRows external upper = upperRows := by
  simp [assemble]

@[simp] theorem assemble_lower (hne : upper ≠ lower)
    (upperRows : Fin (rows (Nodes.height upper)) → H (nodeSlots slots upper))
    (external : OwnInputReference.Exterior slots rows upper lower) :
    assemble slots rows upper lower upperRows external lower = external.lowerRows := by
  simp [assemble, Ne.symm hne]

@[simp] theorem assemble_other
    (upperRows : Fin (rows (Nodes.height upper)) → H (nodeSlots slots upper))
    (external : OwnInputReference.Exterior slots rows upper lower)
    (node : OwnInputReference.OtherNodes upper lower) :
    assemble slots rows upper lower upperRows external node.val = external.otherArrays node := by
  simp only [assemble, dite_eq_right node.property.1, dite_eq_right node.property.2]

theorem assemble_original (arrays : Arrays slots rows) :
    assemble slots rows upper lower (arrays upper) (exteriorOf slots rows upper lower arrays) = arrays := by
  funext node
  by_cases hu : node = upper
  · subst node
    exact assemble_upper slots rows upper lower _ _
  · by_cases hl : node = lower
    · subst node
      simp only [assemble, dite_eq_right hu, dite_eq_left rfl, exteriorOf]
    · simp only [assemble, dite_eq_right hu, dite_eq_right hl, exteriorOf]

def canonicalQuery (a : Block rows lower) (arrays : Arrays slots rows) :=
  BlockQuotient.projectBlock lower a ∘ TreeCanonical.numberedFunction slots (fullJoint arrays)

theorem sampledQuery_eq_reorder (hne : upper ≠ lower) (a : Block rows lower)
    {Ω : Type*} (eval : Ω → OwnInputReference.UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : OwnInputReference.Exterior slots rows upper lower) :
    OwnInputReference.sampledQuery slots rows upper lower a eval tape external =
      reorder rows upper lower hne a ∘ BlockQuotient.projectBlock lower a ∘
        fullJoint (assemble slots rows upper lower
          (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external) := by
  funext x
  apply Prod.ext
  · change (fun row => (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape row).val
        (restrictNode slots upper x)) =
      fun row => ((assemble slots rows upper lower
        (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external) upper row).val
          (restrictNode slots upper x)
    rw [assemble_upper]
  · apply Prod.ext
    · change DirectionQuotient.proj a
          (fun row => (external.lowerRows row).val (restrictNode slots lower x)) =
        DirectionQuotient.proj a
          (fun row => ((assemble slots rows upper lower
            (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external) lower row).val
              (restrictNode slots lower x))
      rw [assemble_lower slots rows upper lower hne]
    · funext node row
      change (external.otherArrays node row).val (restrictNode slots node.val x) =
        ((assemble slots rows upper lower
          (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external) node.val row).val
            (restrictNode slots node.val x)
      rw [assemble_other]

theorem numbered_sampledQuery_eq (hne : upper ≠ lower) (a : Block rows lower)
    {Ω : Type*} (eval : Ω → OwnInputReference.UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : OwnInputReference.Exterior slots rows upper lower) :
    TreeCanonical.numberedFunction slots
      (OwnInputReference.sampledQuery slots rows upper lower a eval tape external) =
      reorder rows upper lower hne a ∘ canonicalQuery slots rows lower a
        (assemble slots rows upper lower
          (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external) := by
  rw [sampledQuery_eq_reorder slots rows upper lower hne a eval tape external]
  rfl

theorem sampled_key_eq (hne : upper ≠ lower) (a : Block rows lower)
    {Ω : Type*} (eval : Ω → OwnInputReference.UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : OwnInputReference.Exterior slots rows upper lower) :
    TreeCanonical.key .right slots
        (OwnInputReference.sampledQuery slots rows upper lower a eval tape external) =
      CanonicalKeys.key .right (TreeCanonical.numberedSlots slots)
        (canonicalQuery slots rows lower a (assemble slots rows upper lower
          (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external)) := by
  unfold TreeCanonical.key
  rw [numbered_sampledQuery_eq slots rows upper lower hne a eval tape external]
  exact CanonicalKeys.key_postcomp_injective .right (TreeCanonical.numberedSlots slots) _
    (reorder rows upper lower hne a) (reorder_injective rows upper lower hne a)

theorem sampled_response_eq (hne : upper ≠ lower) (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    {Ω : Type*} (eval : Ω → OwnInputReference.UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : OwnInputReference.Exterior slots rows upper lower) :
    KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
        (TreeCanonical.numberedFunction slots
          (OwnInputReference.sampledQuery slots rows upper lower a eval tape external)) =
      reorder rows upper lower hne a
        (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
          (canonicalQuery slots rows lower a (assemble slots rows upper lower
            (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external))) := by
  rw [numbered_sampledQuery_eq slots rows upper lower hne a eval tape external]
  exact KeyStrategy.response_postcomp_injective labeling .right
    (TreeCanonical.numberedSlots slots) _ (reorder rows upper lower hne a)
    (reorder_injective rows upper lower hne a)

theorem response_readInput_hidden_eq (hne : upper ≠ lower)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper)) (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    {Ω : Type*} (eval : Ω → OwnInputReference.UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : OwnInputReference.Exterior slots rows upper lower) :
    OwnInputReference.response slots rows upper lower W a labeling
        (OwnInputReference.readInput slots rows upper lower W a eval
          ((HiddenBucketBias.splitTape W Ω tape).2, external))
        (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω tape).1) =
      (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
        (canonicalQuery slots rows lower a (assemble slots rows upper lower
          (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external))).2.1
            ⟨upper, hne⟩ := by
  rw [OwnInputReference.response_readInput_hidden]
  exact congrArg Prod.fst (sampled_response_eq slots rows upper lower hne a labeling eval tape external)

theorem response_readInput_hidden_arrays (hne : upper ≠ lower)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper)) (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    {Ω : Type*} (eval : Ω → OwnInputReference.UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω) (arrays : Arrays slots rows)
    (hupper : BucketSampler.evaluate (rows (Nodes.height upper)) eval tape = arrays upper) :
    OwnInputReference.response slots rows upper lower W a labeling
        (OwnInputReference.readInput slots rows upper lower W a eval
          ((HiddenBucketBias.splitTape W Ω tape).2, exteriorOf slots rows upper lower arrays))
        (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω tape).1) =
      (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
        (canonicalQuery slots rows lower a arrays)).2.1 ⟨upper, hne⟩ := by
  rw [response_readInput_hidden_eq slots rows upper lower hne W a labeling eval tape]
  rw [hupper, assemble_original]

end
end PerfectCompleteness.OwnInputCanonicalQuery

end OAI
