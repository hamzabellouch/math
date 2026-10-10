import OAI.Computability.PerfectCompleteness.Decoding.CleanDecoderSeedLawLemmas
import OAI.Computability.PerfectCompleteness.Decoding.CleanRecordProjection
import OAI.Computability.PerfectCompleteness.Foundations.WholeReplaySubtreeLemmas
import OAI.Computability.PerfectCompleteness.Machines.WholeArrayInteriorOwnInputLaw
import OAI.Computability.PerfectCompleteness.Repetition.CleanNativeReplay

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalDecoderLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

attribute [local instance] RightDecoder.scalarFintype

local instance nativeLeftFintype {branch : Nat → Nat} {n t : Nat}
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

section NativeData

variable {branch rows repeats : Nat → Nat} {n t : Nat}

def inputOfArrays (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch n) (W : Submodule F2 (Block rows upper))
    (a : Block rows lower)
    (known : HiddenBucketBias.VisibleDirection W → H (nodeSlots slots upper))
    (arrays : Arrays slots rows) : OwnInputReference.Input slots rows upper lower W a where
  knownBuckets := known
  otherArrays node := arrays node.val
  lowerQuotient x := DirectionQuotient.proj a (fun row => (arrays lower row).val x)

private theorem inputOfArrays_heq
    (slots target : Slots branch n → Fin t → MixedSupport.Slot) (hs : slots = target)
    (upper lower : Nodes branch n) (W : Submodule F2 (Block rows upper))
    (a : Block rows lower)
    (known : HiddenBucketBias.VisibleDirection W → H (nodeSlots slots upper))
    (otherKnown : HiddenBucketBias.VisibleDirection W → H (nodeSlots target upper))
    (hk : HEq known otherKnown) (arrays : Arrays slots rows) (other : Arrays target rows)
    (ha : HEq arrays other) :
    HEq (inputOfArrays slots upper lower W a known arrays)
      (inputOfArrays target upper lower W a otherKnown other) := by
  cases hs
  cases eq_of_heq hk
  cases eq_of_heq ha
  rfl

private theorem replayKnown_heq {h : Nat}
    (slots target : Slots branch n → Fin t → MixedSupport.Slot) (hs : slots = target)
    (upper : Nodes branch n) (p : Path branch (Nodes.height upper) (h + 1))
    (hp : h + 1 < Nodes.height upper) (clean : Fin (branch h) → Prop)
    (W : Submodule F2 (Block rows upper))
    (tape : WholeCutReplay.Tape rows repeats ((Nodes.path upper).append p) slots clean)
    (other : WholeCutReplay.Tape rows repeats ((Nodes.path upper).append p) target clean)
    (ht : HEq tape other) :
    HEq (WholeReplaySubtree.knownBucketsAtNode rows repeats slots upper p hp clean W tape)
      (WholeReplaySubtree.knownBucketsAtNode rows repeats target upper p hp clean W other) := by
  cases hs
  cases eq_of_heq ht
  rfl

def uncastTape (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch n) (cut : OwnInputReference.Cut upper lower)
    {k : Nat} (hk : Nodes.height lower = k)
    (tape : WholeArraySampler.Tape rows repeats
      ((Nodes.path upper).append (hk ▸ cut.path)) slots) :
    WholeArraySampler.Tape rows repeats ((Nodes.path upper).append cut.path) slots := by
  cases hk
  exact tape

def inputFromTape (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch n) (cut : OwnInputReference.Cut upper lower)
    {k : Nat} (hk : Nodes.height lower = k)
    (W : Submodule F2 (Block rows upper)) (a : Block rows lower)
    (tape : WholeArraySampler.Tape rows repeats
      ((Nodes.path upper).append (hk ▸ cut.path)) slots) :
    OwnInputReference.Input slots rows upper lower W a :=
  inputOfArrays slots upper lower W a
    (fun v => RecursiveSampler.evaluate F2 repeats (hk ▸ cut.path)
      (LeafDomain (nodeSlots slots upper))
      ((WholeArrayPositiveSplit.split rows repeats (Nodes.path upper) (hk ▸ cut.path)
        (by simpa only [hk] using cut.proper) slots W tape).2.1 v))
    (WholeArraySampler.evaluate rows repeats ((Nodes.path upper).append (hk ▸ cut.path)) slots tape)

theorem inputFromTape_eq_ownInput
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch n) (cut : OwnInputReference.Cut upper lower)
    {k : Nat} (hk : Nodes.height lower = k)
    (W : Submodule F2 (Block rows upper)) (a : Block rows lower)
    (tape : WholeArraySampler.Tape rows repeats
      ((Nodes.path upper).append (hk ▸ cut.path)) slots) :
    inputFromTape slots upper lower cut hk W a tape =
      WholeArrayInteriorOwnInputLaw.ownInput rows repeats slots upper lower cut W a
        (uncastTape slots upper lower cut hk tape) := by
  cases hk
  rfl

variable {Sample : OriginalDecoderMark.SlotFamily branch n t → Type*}
  [∀ slots, Fintype (Sample slots)]
  (F : OriginalDecoderMark.Family branch rows n t Sample)

def adviceLaw (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (upper : Nodes branch n) (level : Nat) (κ : ℝ)
    (arrays : Arrays slots rows)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r) :
    FiniteDistribution (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  HierarchicalLeftDecoder.adviceLaw slots upper level
    (HierarchicalMatrixTable.backgroundOf slots upper arrays) σ
    (OriginalDecoderMark.mark F upper level κ slots
      (HierarchicalMatrixTable.backgroundOf slots upper arrays)) r ρ A
    (A.comp (MatrixRowQuotient.projectMatrix
      (HierarchicalFrozenTables.knownRows slots upper level
        (HierarchicalMatrixTable.backgroundOf slots upper arrays))
      (NodeEmbedding.matrix arrays upper)))

private theorem adviceLaw_heq
    (slots target : Slots branch n → Fin t → MixedSupport.Slot) (hs : slots = target)
    (upper : Nodes branch n) (level : Nat) (κ : ℝ)
    (arrays : Arrays slots rows) (other : Arrays target rows) (ha : HEq arrays other)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r) :
    HEq (adviceLaw F slots upper level κ arrays σ r ρ A)
      (adviceLaw F target upper level κ other σ r ρ A) := by
  cases hs
  cases eq_of_heq ha
  rfl

private theorem rightLaw_heq
    (slots target : Slots branch n → Fin t → MixedSupport.Slot) (hs : slots = target)
    (upper lower : Nodes branch n) (W : Submodule F2 (Block rows upper))
    (a : Block rows lower) (cut : OwnInputReference.Cut upper lower)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (input : OwnInputReference.Input slots rows upper lower W a)
    (other : OwnInputReference.Input target rows upper lower W a) (hi : HEq input other)
    (threshold : ℝ) :
    HEq (RightDecoder.law slots rows upper lower W a repeats cut σ input threshold)
      (RightDecoder.law target rows upper lower W a repeats cut σ other threshold) := by
  cases hs
  cases eq_of_heq hi
  rfl

abbrev Answers (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (upper : Nodes branch n) :=
  Module.Dual F2 (NodeEmbedding.RowSpace slots upper) ×
    Module.Dual F2 (OwnInputReference.UpperSpace projected upper)

instance answersFintype (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (upper : Nodes branch n) : Fintype (Answers slots projected upper) := by
  letI := LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
  letI := RightDecoder.scalarFintype projected upper
  exact inferInstanceAs (Fintype
    (Module.Dual F2 (NodeEmbedding.RowSpace slots upper) ×
      Module.Dual F2 (OwnInputReference.UpperSpace projected upper)))

def answerEquiv (slots projected target other : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : slots = target) (hp : projected = other) (upper : Nodes branch n) :
    Answers slots projected upper ≃ Answers target other upper := by
  cases hs
  cases hp
  exact Equiv.refl _

private theorem product_heq
    (slots projected target other : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : slots = target) (hp : projected = other) (upper : Nodes branch n)
    (μ : FiniteDistribution (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)))
    (μ' : FiniteDistribution (Module.Dual F2 (NodeEmbedding.RowSpace target upper)))
    (ν : FiniteDistribution (Module.Dual F2 (OwnInputReference.UpperSpace projected upper)))
    (ν' : FiniteDistribution (Module.Dual F2 (OwnInputReference.UpperSpace other upper)))
    (hμ : HEq μ μ') (hν : HEq ν ν') : HEq (μ.product ν) (μ'.product ν') := by
  cases hs
  cases hp
  cases eq_of_heq hμ
  cases eq_of_heq hν
  rfl

private theorem pushforward_answerEquiv
    (slots projected target other : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : slots = target) (hp : projected = other) (upper : Nodes branch n)
    (μ : FiniteDistribution (Answers slots projected upper))
    (ν : FiniteDistribution (Answers target other upper)) (hμ : HEq μ ν) :
    μ.pushforward (answerEquiv slots projected target other hs hp upper) = ν := by
  cases hs
  cases hp
  cases eq_of_heq hμ
  exact FiniteDistribution.pushforward_id μ

private theorem meeting_answerEquiv
    (slots projected target other : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : slots = target) (hp : projected = other) (upper : Nodes branch n)
    (q : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (q' : ∀ s k, MixedSupport.Projection (target s k) (other s k))
    (hq : ∀ s k, HEq (q s k) (q' s k)) (answer : Answers slots projected upper) :
    decide ((answerEquiv slots projected target other hs hp upper answer).2 =
      DecoderSourcePullback.upperTarget q' upper
        (answerEquiv slots projected target other hs hp upper answer).1) =
      decide (answer.2 = DecoderSourcePullback.upperTarget q upper answer.1) := by
  cases hs
  cases hp
  have hqq : q = q' := funext (fun s => funext (fun k => eq_of_heq (hq s k)))
  cases hqq
  rfl

end NativeData

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

abbrev lower (_S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d) :=
  HierarchicalLeftDecoder.LowerNode upper (h + 1) d

abbrev leftArrays (x : CleanDecoderRate.Sample S) :=
  WholeCutSampler.evaluate rows repeats (CleanDecoderRate.path S)
    (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.leftTape S x)

abbrev rightArrays (x : CleanDecoderRate.Sample S) :=
  WholeCutSampler.evaluate rows repeats (CleanDecoderRate.path S)
    (CleanNativeReplay.rightSlots S x) (CleanNativeReplay.rightTape S x)

abbrev rightWholeTape (x : CleanDecoderRate.Sample S) :=
  WholeCutSampler.collapse rows repeats (CleanDecoderRate.path S)
    (CleanNativeReplay.rightSlots S x) (CleanNativeReplay.rightTape S x)

def rightInput (W : Submodule F2 (Block rows upper)) (a : Block rows (lower S))
    (x : CleanDecoderRate.Sample S) :
    OwnInputReference.Input (CleanNativeReplay.rightSlots S x) rows upper (lower S) W a :=
  inputFromTape (CleanNativeReplay.rightSlots S x) upper (lower S) S.cut
    (CleanDecoderContext.lowerHeight upper d) W a (rightWholeTape S x)

theorem rightInput_eq_ownInput (W : Submodule F2 (Block rows upper))
    (a : Block rows (lower S)) (x : CleanDecoderRate.Sample S) :
    rightInput S W a x =
      WholeArrayInteriorOwnInputLaw.ownInput rows repeats (CleanNativeReplay.rightSlots S x)
        upper (lower S) S.cut W a
        (uncastTape (CleanNativeReplay.rightSlots S x) upper (lower S) S.cut
          (CleanDecoderContext.lowerHeight upper d) (rightWholeTape S x)) :=
  inputFromTape_eq_ownInput _ _ _ _ _ _ _ _

variable {Sample : OriginalDecoderMark.SlotFamily branch n t → Type*}
  [∀ slots, Fintype (Sample slots)]
  (F : OriginalDecoderMark.Family branch rows n t Sample) (κ : ℝ)

def useful (record : CleanDecoderRate.Record S) :=
  OriginalDecoderMark.useful F upper (h + 1) κ
    (CleanDecoderContext.leftExposed (CleanDecoderRate.context S record))

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (W : Submodule F2 (Block rows upper)) (a : Block rows (lower S))
  (threshold : ℝ)

def leftLaw (x : CleanDecoderRate.Sample S) :=
  adviceLaw F (CleanNativeReplay.leftSlots S x) upper (h + 1) κ (leftArrays S x) σ r ρ A

def rightLaw (x : CleanDecoderRate.Sample S) :=
  RightDecoder.law (CleanNativeReplay.rightSlots S x) rows upper (lower S) W a
    repeats S.cut σ (rightInput S W a x) threshold

def pairKernel (x : CleanDecoderRate.Sample S) :=
  (leftLaw S F κ σ r ρ A x).product (rightLaw S σ W a threshold x)

variable (cube : Nat) (hcube : 0 < cube)

theorem leftKernel_heq (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    HEq (CleanDecoderSeedLaw.leftKernel (CleanDecoderPairLaw.context S x) σ
      (useful S F κ (CleanDecoderRate.observations S x)) r ρ A (CleanDecoderPairLaw.leftOwn S x))
      (leftLaw S F κ σ r ρ A x) :=
  adviceLaw_heq F _ _ (CleanNativeReplay.leftSlots_eq S x) upper (h + 1) κ
    _ _ (CleanNativeReplay.leftArrays_heq S cube hcube x hx) σ r ρ A

theorem rightKnownBuckets_heq (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    HEq (CleanRightDecoder.knownBuckets
      (CleanDecoderPairLaw.context S x).clauses (CleanDecoderPairLaw.context S x).designated
      (CleanDecoderPairLaw.context S x).clean (CleanDecoderPairLaw.context S x).visible
      (CleanDecoderPairLaw.context S x).projected upper (lower S) S.cut
      (CleanDecoderContext.lowerHeight upper d) S.outside rows repeats
      (CleanDecoderPairLaw.context S x).rightTape W (CleanDecoderPairLaw.rightOwn S x))
      (rightInput S W a x).knownBuckets := by
  let suffix := CleanRightDecoder.suffix upper (lower S) S.cut
    (CleanDecoderContext.lowerHeight upper d)
  have hp : h + 1 < Nodes.height upper :=
    CleanRightDecoder.suffix_proper upper (lower S) S.cut (CleanDecoderContext.lowerHeight upper d)
  have hzero := (WholeCutZero.grouped_iff rows repeats (CleanDecoderRate.path S)
    (CleanNativeReplay.rightSlots S x) (CleanDecoderPairLaw.context S x).clean
    (CleanNativeReplay.rightTape S x)).mp (CleanNativeReplay.right_grouped_zero S cube hcube x hx)
  have h := replayKnown_heq _ _ (CleanNativeReplay.rightSlots_eq S x) upper suffix hp
    (CleanDecoderPairLaw.context S x).clean W _ _ (CleanNativeReplay.rightReplay_heq S x)
  have he := WholeCutSubtree.knownBucketsAtNode_erase rows repeats
    (CleanNativeReplay.rightSlots S x) upper suffix hp (CleanDecoderPairLaw.context S x).clean
    W (CleanNativeReplay.rightTape S x) hzero
  have ho := WholeCutSubtree.knownBuckets_eq_original rows repeats (Nodes.path upper) suffix hp
    (CleanNativeReplay.rightSlots S x) W (CleanNativeReplay.rightTape S x)
  exact h.trans ((heq_of_eq he).trans (heq_of_eq ho))

theorem rightInput_heq (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    HEq (CleanRightDecoder.input
      (CleanDecoderPairLaw.context S x).clauses (CleanDecoderPairLaw.context S x).designated
      (CleanDecoderPairLaw.context S x).clean (CleanDecoderPairLaw.context S x).visible
      (CleanDecoderPairLaw.context S x).projected upper (lower S) S.cut
      (CleanDecoderContext.lowerHeight upper d) S.outside rows repeats
      (CleanDecoderPairLaw.context S x).rightTape W a (CleanDecoderPairLaw.rightOwn S x))
      (rightInput S W a x) :=
  inputOfArrays_heq _ _ (CleanNativeReplay.rightSlots_eq S x) upper (lower S) W a
    _ _ (rightKnownBuckets_heq S W a cube hcube x hx)
    _ _ (CleanNativeReplay.rightArrays_heq S cube hcube x hx)

theorem rightKernel_heq (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    HEq (CleanDecoderSeedLaw.rightKernel (CleanDecoderPairLaw.context S x) σ W a threshold
      (CleanDecoderPairLaw.rightOwn S x)) (rightLaw S σ W a threshold x) :=
  rightLaw_heq _ _ (CleanNativeReplay.rightSlots_eq S x) upper (lower S) W a S.cut σ
    _ _ (rightInput_heq S W a cube hcube x hx) threshold

theorem pairKernel_heq (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    HEq (CleanDecoderPairLaw.pairKernel S σ (useful S F κ) r ρ A W a threshold x)
      (pairKernel S F κ σ r ρ A W a threshold x) :=
  product_heq _ _ _ _ (CleanNativeReplay.leftSlots_eq S x)
    (CleanNativeReplay.rightSlots_eq S x) upper _ _ _ _
    (leftKernel_heq S F κ σ r ρ A cube hcube x hx)
    (rightKernel_heq S σ W a threshold cube hcube x hx)

def physicalAnswerEquiv (x : CleanDecoderRate.Sample S) :
    CleanDecoderPairLaw.Pair S x ≃
      Answers (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x) upper :=
  answerEquiv _ _ _ _ (CleanNativeReplay.leftSlots_eq S x)
    (CleanNativeReplay.rightSlots_eq S x) upper

theorem pairKernel_pushforward (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    (CleanDecoderPairLaw.pairKernel S σ (useful S F κ) r ρ A W a threshold x).pushforward
        (physicalAnswerEquiv S x) = pairKernel S F κ σ r ρ A W a threshold x :=
  pushforward_answerEquiv _ _ _ _ (CleanNativeReplay.leftSlots_eq S x)
    (CleanNativeReplay.rightSlots_eq S x) upper _ _
    (pairKernel_heq S F κ σ r ρ A W a threshold cube hcube x hx)

theorem probability_pairKernel (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0)
    (event : Answers (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x) upper → Bool) :
    (pairKernel S F κ σ r ρ A W a threshold x).probability event =
      (CleanDecoderPairLaw.pairKernel S σ (useful S F κ) r ρ A W a threshold x).probability
        (fun answer => event (physicalAnswerEquiv S x answer)) := by
  rw [← pairKernel_pushforward S F κ σ r ρ A W a threshold cube hcube x hx]
  exact FiniteDistribution.probability_pushforward _ _ _

abbrev physicalProjection (x : CleanDecoderRate.Sample S) :=
  CleanPhysicalCanonicalQuery.projection rows repeats (CleanDecoderRate.path S)
    S.outside S.clauses S.designated x

theorem projection_heq (x : CleanDecoderRate.Sample S) (leaf : Slots branch n) (k : Fin t) :
    HEq (CleanDecoderOddLists.fullProjection (CleanDecoderPairLaw.context S x)
      (CleanDecoderPairLaw.occurrences S x) leaf k) (physicalProjection S x leaf k) :=
  CleanRecordProjection.decoderProjection_heq rows S.clauses S.designated repeats upper d S.cut
    S.outside S.placeholder (CleanDecoderRate.observations S x) S.exterior x
    (CleanRecordDecoderInput.event_observe rows repeats upper d S.cut S.clauses S.designated x) leaf k

theorem meeting_probability_eq (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    (pairKernel S F κ σ r ρ A W a threshold x).probability
      (fun answer => decide (answer.2 = DecoderSourcePullback.upperTarget
        (physicalProjection S x) upper answer.1)) =
      (CleanDecoderPairLaw.pairKernel S σ (useful S F κ) r ρ A W a threshold x).probability
        (fun answer => decide (answer.2 = DecoderSourcePullback.upperTarget
          (CleanDecoderOddLists.fullProjection (CleanDecoderPairLaw.context S x)
            (CleanDecoderPairLaw.occurrences S x)) upper answer.1)) := by
  rw [probability_pairKernel S F κ σ r ρ A W a threshold cube hcube x hx]
  congr 1
  funext answer
  exact meeting_answerEquiv _ _ _ _ (CleanNativeReplay.leftSlots_eq S x)
    (CleanNativeReplay.rightSlots_eq S x) upper _ _ (projection_heq S x) answer

end
end PerfectCompleteness.CleanPhysicalDecoderLaw

end

end OAI
