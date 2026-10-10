import OAI.Computability.PerfectCompleteness.Decoding.DecoderSourcePullback
import OAI.Computability.PerfectCompleteness.Decoding.HierarchicalLeftDecoder
import OAI.Computability.PerfectCompleteness.Decoding.RightDecoderLemmas
import OAI.Computability.PerfectCompleteness.Decoding.TwoResponseCollisionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutReplayLemmas
import OAI.Computability.PerfectCompleteness.Foundations.WholeReplaySubtreeLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanEndpointSlots
import OAI.Computability.PerfectCompleteness.Sampling.RecursiveSamplerLaws

namespace OAI

section

namespace PerfectCompleteness.CleanLeftDecoder

noncomputable section

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

structure Exposed (branch rows repeats : Nat → Nat) (n h t v m : Nat) [NeZero m] where
  clauses : Fin m → SourceClause.NormalizedClause v
  designated : Fin (branch h) → Slots branch h
  clean : Fin (branch h) → Prop
  visible : SourceQuestionReconstruction.Visible
    (E := SourceQuestionReconstruction.SourceTuple m t) designated clean
  path : Path branch n (h + 1)
  outside : Slots branch n → Fin t → MixedSupport.Slot
  tape : WholeCutReplay.Tape rows repeats path
    (CutSlotAssembly.fill path outside
      (CleanEndpointSlots.leftReference clauses designated clean visible)) clean

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  (E : Exposed branch rows repeats n h t v m)

abbrev Own := {i : Fin (branch h) // E.clean i} → Fin t → Fin m

instance ownFintype : Fintype (Own E) := Fintype.ofFinite _

def slots (own : Own E) : Slots branch n → Fin t → MixedSupport.Slot :=
  CleanEndpointSlots.leftSlots E.clauses E.designated E.clean E.visible E.path E.outside own

def replay (own : Own E) : WholeCutReplay.Tape rows repeats E.path (slots E own) E.clean :=
  CleanEndpointSlots.leftReplay E.clauses E.designated E.clean E.visible
    rows repeats E.path E.outside E.tape own

def arrays (own : Own E) : Arrays (slots E own) rows :=
  WholeCutReplay.evaluateArrays rows repeats E.path (slots E own) E.clean (replay E own)

variable (upper : Nodes branch n) (lowerLevel : Nat)

def background (own : Own E) :
    HierarchicalMatrixTable.Background (rows := rows) (slots E own) upper :=
  HierarchicalMatrixTable.backgroundOf (slots E own) upper (arrays E own)

def upperMatrix (own : Own E) :
    HierarchicalMatrixTable.Matrix (rows := rows) (slots E own) upper :=
  NodeEmbedding.matrix (arrays E own) upper

def quotientMatrix (own : Own E) :
    HierarchicalFrozenTables.QuotientMatrix (slots E own) upper lowerLevel
      (background E upper own) :=
  MatrixRowQuotient.projectMatrix
    (HierarchicalFrozenTables.knownRows (slots E own) upper lowerLevel (background E upper own))
    (upperMatrix E upper own)

abbrev QuotientAdvice (r : Nat) (own : Own E) :=
  Module.Dual F2 (NodeEmbedding.RowSpace (slots E own) upper ⧸
    HierarchicalFrozenTables.knownRows (slots E own) upper lowerLevel (background E upper own))
      →ₗ[F2] (Fin r → F2)

def advice (r : Nat) (A : ManyGoodRows.RowMap (Block rows upper) r) (own : Own E) :
    ManyGoodRows.RowMap (Block rows upper) r × QuotientAdvice E upper lowerLevel r own :=
  (A, A.comp (quotientMatrix E upper lowerLevel own))

abbrev UpperAnswer (own : Own E) := Module.Dual F2 (NodeEmbedding.RowSpace (slots E own) upper)

local instance rowSpaceFintype (own : Own E) (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace (slots E own) node) := Fintype.ofFinite _

local instance nodeSpaceFintype (own : Own E) (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH (slots E own) node) := Fintype.ofFinite _

instance upperAnswerFintype (own : Own E) : Fintype (UpperAnswer E upper own) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace (slots E own) upper)

abbrev Useful := (own : Own E) →
  HierarchicalFrozenTables.QuotientMatrix (slots E own) upper lowerLevel
    (background E upper own) → Prop

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : Useful E upper lowerLevel)

def law (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r) (own : Own E) :
    FiniteDistribution (UpperAnswer E upper own) :=
  HierarchicalLeftDecoder.adviceLaw (slots E own) upper lowerLevel (background E upper own)
    σ (useful own) r ρ (advice E upper lowerLevel r A own).1
      (advice E upper lowerLevel r A own).2

abbrev Seed := (own : Own E) → UpperAnswer E upper own

def seedLaw (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r) :
    FiniteDistribution (Seed E upper) :=
  FiniteProduct.law (I := Own E) (Ω := UpperAnswer E upper)
    (law E upper lowerLevel σ useful r ρ A)

theorem seedLaw_marginal (r : Nat) (ρ : ℝ)
    (A : ManyGoodRows.RowMap (Block rows upper) r) (own : Own E) :
    (seedLaw E upper lowerLevel σ useful r ρ A).pushforward (fun seed => seed own) =
      law E upper lowerLevel σ useful r ρ A own :=
  FiniteProduct.eval_pushforward (I := Own E) (Ω := UpperAnswer E upper)
    (law E upper lowerLevel σ useful r ρ A) own

theorem supported_row (r : Nat) (ρ : ℝ)
    (A : ManyGoodRows.RowMap (Block rows upper) r) (seed : Seed E upper)
    (hsupport : (seedLaw E upper lowerLevel σ useful r ρ A).weight seed ≠ 0)
    (own : Own E) : (law E upper lowerLevel σ useful r ρ A own).weight (seed own) ≠ 0 := by
  intro hz
  apply hsupport
  change (∏ q, (law E upper lowerLevel σ useful r ρ A q).weight (seed q)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ own) hz

variable (hbranch : ∀ k < n, 0 < branch k)

theorem law_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (A : ManyGoodRows.RowMap (Block rows upper) r) (own : Own E) :
    (law E upper lowerLevel σ useful r ρ A own).probability
      (fun q => decide (HierarchicalLeftDecoder.Valid (slots E own) upper lowerLevel
        hbranch (background E upper own) q)) = 1 :=
  HierarchicalLeftDecoder.adviceLaw_valid (slots E own) upper lowerLevel hbranch
    (background E upper own) σ (useful own) r ρ hρ
    (advice E upper lowerLevel r A own).1 (advice E upper lowerLevel r A own).2

theorem supported_seed_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (A : ManyGoodRows.RowMap (Block rows upper) r) (seed : Seed E upper)
    (hsupport : (seedLaw E upper lowerLevel σ useful r ρ A).weight seed ≠ 0)
    (own : Own E) :
    HierarchicalLeftDecoder.Valid (slots E own) upper lowerLevel hbranch
      (background E upper own) (seed own) := by
  exact of_decide_eq_true (DecoderTableAdmissibility.event_of_probability_one
    (law E upper lowerLevel σ useful r ρ A own)
    (fun q => decide (HierarchicalLeftDecoder.Valid (slots E own) upper lowerLevel
      hbranch (background E upper own) q))
    (law_valid E upper lowerLevel σ useful hbranch r ρ hρ A own) (seed own)
    (supported_row E upper lowerLevel σ useful r ρ A seed hsupport own))

theorem seedLaw_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (A : ManyGoodRows.RowMap (Block rows upper) r) :
    (seedLaw E upper lowerLevel σ useful r ρ A).probability
      (fun seed => decide (∀ own : Own E,
        HierarchicalLeftDecoder.Valid (slots E own) upper lowerLevel hbranch
          (background E upper own) (seed own))) = 1 := by
  apply DecoderTableAdmissibility.probability_one_of_support
  intro seed hs
  exact decide_eq_true (supported_seed_valid E upper lowerLevel σ useful hbranch
    r ρ hρ A seed hs)

abbrev LowerH (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (own : Own E) :=
  NodeEmbedding.NodeH (slots E own) (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

abbrev LowerAnswer (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (own : Own E) :=
  Module.Dual F2 (squareSpace (LowerH E upper lowerLevel d own))

instance lowerAnswerFintype (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (own : Own E) : Fintype (LowerAnswer E upper lowerLevel d own) :=
  LeftDecoder.dualFintype (V := squareSpace (LowerH E upper lowerLevel d own))

def output (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (own : Own E)
    (q : UpperAnswer E upper own) : LowerAnswer E upper lowerLevel d own :=
  HierarchicalLeftDecoder.output (slots E own) upper lowerLevel hbranch d q

def form (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (own : Own E)
    (q : UpperAnswer E upper own) :
    LowerH E upper lowerLevel d own →ₗ[F2] LowerH E upper lowerLevel d own →ₗ[F2] F2 :=
  OddListExtraction.multiplicationForm (LowerH E upper lowerLevel d own)
    (output E upper lowerLevel hbranch d own q)

def formFamily (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (seed : Seed E upper) :
    (own : Own E) →
      LowerH E upper lowerLevel d own →ₗ[F2] LowerH E upper lowerLevel d own →ₗ[F2] F2 :=
  fun own => form E upper lowerLevel hbranch d own (seed own)

def outputLaw (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (own : Own E) :
    FiniteDistribution (LowerAnswer E upper lowerLevel d own) :=
  (law E upper lowerLevel σ useful r ρ A own).pushforward
    (output E upper lowerLevel hbranch d own)

theorem seedLaw_output_marginal (r : Nat) (ρ : ℝ)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (own : Own E) :
    (seedLaw E upper lowerLevel σ useful r ρ A).pushforward
      (fun seed => output E upper lowerLevel hbranch d own (seed own)) =
        outputLaw E upper lowerLevel σ useful hbranch r ρ A d own := by
  calc
    _ = ((seedLaw E upper lowerLevel σ useful r ρ A).pushforward
        (fun seed : Seed E upper => seed own)).pushforward
          (output E upper lowerLevel hbranch d own) :=
      (FiniteDistribution.pushforward_comp (seedLaw E upper lowerLevel σ useful r ρ A)
        (fun seed : Seed E upper => seed own) (output E upper lowerLevel hbranch d own)).symm
    _ = _ := by rw [seedLaw_marginal]; rfl

theorem supported_output_normalized (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (A : ManyGoodRows.RowMap (Block rows upper) r) (seed : Seed E upper)
    (hsupport : (seedLaw E upper lowerLevel σ useful r ρ A).weight seed ≠ 0)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (own : Own E) :
    output E upper lowerLevel hbranch d own (seed own)
      (HierarchicalLeftDecoder.lowerOne (slots E own) upper lowerLevel hbranch d) = 1 :=
  (supported_seed_valid E upper lowerLevel σ useful hbranch r ρ hρ A seed hsupport own d).1

theorem supported_form_tested_rank (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (A : ManyGoodRows.RowMap (Block rows upper) r) (seed : Seed E upper)
    (hsupport : (seedLaw E upper lowerLevel σ useful r ρ A).weight seed ≠ 0)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (own : Own E) :
    (LowerAffineSliceRank.testedGram
      (FunctionSpaceLowerRank.matrixForm (LowerH E upper lowerLevel d own)
        (formFamily E upper lowerLevel hbranch d seed own))
      (HierarchicalLeftDecoder.testedMatrix (slots E own) upper lowerLevel
        (background E upper own) d)).rank ≤ 1 :=
  (supported_seed_valid E upper lowerLevel σ useful hbranch r ρ hρ A seed hsupport own d).2

end
end PerfectCompleteness.CleanLeftDecoder

end

section

namespace PerfectCompleteness.CleanRightDecoder

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {N h : Nat}

def suffix (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (hlower : Nodes.height lower = h + 1) : Path branch (Nodes.height upper) (h + 1) :=
  hlower ▸ cut.path

theorem suffix_proper (upper lower : Nodes branch N)
    (cut : OwnInputReference.Cut upper lower) (hlower : Nodes.height lower = h + 1) :
    h + 1 < Nodes.height upper := by
  simpa only [hlower] using cut.proper

def fullPath (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (hlower : Nodes.height lower = h + 1) : Path branch N (h + 1) :=
  (Nodes.path upper).append (suffix upper lower cut hlower)

variable {t v m : Nat}

abbrev OwnQuestions (clean : Fin (branch h) → Prop) :=
  {i : Fin (branch h) // clean i} → Fin t → Fin v

variable [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)
  (clean : Fin (branch h) → Prop)
  (visible : SourceQuestionReconstruction.Visible
    (E := SourceQuestionReconstruction.SourceTuple m t) designated clean)
  (projected : Fin (branch h) → Bool)
  (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
  (hlower : Nodes.height lower = h + 1)
  (outside : Slots branch N → Fin t → MixedSupport.Slot)

def slots (own : OwnQuestions (t := t) (v := v) clean) :
    Slots branch N → Fin t → MixedSupport.Slot :=
  CleanEndpointSlots.rightSlots clauses designated clean visible
    (fullPath upper lower cut hlower) outside projected own

variable (rows repeats : Nat → Nat)

abbrev Record := WholeCutReplay.Tape rows repeats (fullPath upper lower cut hlower)
  (CutSlotAssembly.fill (fullPath upper lower cut hlower) outside
    (CleanEndpointSlots.rightReference clauses designated clean visible projected)) clean

variable (record : Record clauses designated clean visible projected
  upper lower cut hlower outside rows repeats)

def replay (own : OwnQuestions (t := t) (v := v) clean) :
    WholeCutReplay.Tape rows repeats (fullPath upper lower cut hlower)
      (slots clauses designated clean visible projected upper lower cut hlower outside own) clean :=
  CleanEndpointSlots.rightReplay clauses designated clean visible rows repeats
    (fullPath upper lower cut hlower) outside projected record own

def arrays (own : OwnQuestions (t := t) (v := v) clean) :
    Arrays (slots clauses designated clean visible projected upper lower cut hlower outside own) rows :=
  WholeCutReplay.evaluateArrays rows repeats (fullPath upper lower cut hlower)
    (slots clauses designated clean visible projected upper lower cut hlower outside own) clean
    (replay clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record own)

def exterior (own : OwnQuestions (t := t) (v := v) clean) :
    OwnInputReference.Exterior
      (slots clauses designated clean visible projected upper lower cut hlower outside own)
      rows upper lower where
  otherArrays node := arrays clauses designated clean visible projected
    upper lower cut hlower outside rows repeats record own node.val
  lowerRows := arrays clauses designated clean visible projected
    upper lower cut hlower outside rows repeats record own lower

variable (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
  (a : OwnInputReference.LowerVector rows lower)

def knownBuckets (own : OwnQuestions (t := t) (v := v) clean) :
    HiddenBucketBias.VisibleDirection W →
      OwnInputReference.UpperSpace
        (slots clauses designated clean visible projected upper lower cut hlower outside own) upper :=
  WholeReplaySubtree.knownBucketsAtNode rows repeats
    (slots clauses designated clean visible projected upper lower cut hlower outside own)
    upper (suffix upper lower cut hlower) (suffix_proper upper lower cut hlower) clean W
    (replay clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record own)

def input (own : OwnQuestions (t := t) (v := v) clean) :
    OwnInputReference.Input
      (slots clauses designated clean visible projected upper lower cut hlower outside own)
      rows upper lower W a :=
  OwnInputReference.readInput
    (slots clauses designated clean visible projected upper lower cut hlower outside own)
    rows upper lower W a id
    (knownBuckets clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W own,
      exterior clauses designated clean visible projected upper lower cut hlower outside
        rows repeats record own)

@[simp] theorem input_knownBuckets (own : OwnQuestions (t := t) (v := v) clean) :
    (input clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a own).knownBuckets =
      knownBuckets clauses designated clean visible projected upper lower cut hlower outside
        rows repeats record W own := rfl

@[simp] theorem input_otherArrays (own : OwnQuestions (t := t) (v := v) clean)
    (node : OwnInputReference.OtherNodes upper lower) :
    (input clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a own).otherArrays node =
      arrays clauses designated clean visible projected upper lower cut hlower outside
        rows repeats record own node.val := rfl

@[simp] theorem input_lowerQuotient (own : OwnQuestions (t := t) (v := v) clean)
    (x : Domain (nodeSlots
      (slots clauses designated clean visible projected upper lower cut hlower outside own) lower)) :
    (input clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a own).lowerQuotient x =
      DirectionQuotient.proj a (fun row =>
        (arrays clauses designated clean visible projected upper lower cut hlower outside
          rows repeats record own lower row).val x) := rfl

abbrev Answer (own : OwnQuestions (t := t) (v := v) clean) :=
  Module.Dual F2 (OwnInputReference.UpperSpace
    (slots clauses designated clean visible projected upper lower cut hlower outside own) upper)

local instance answerFintype (own : OwnQuestions (t := t) (v := v) clean) :
    Fintype (Answer clauses designated clean visible projected upper lower cut hlower outside own) :=
  RightDecoder.scalarFintype
    (slots clauses designated clean visible projected upper lower cut hlower outside own) upper

variable (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch N t))
  (threshold : ℝ)

def kernel (own : OwnQuestions (t := t) (v := v) clean) :
    FiniteDistribution (Answer clauses designated clean visible projected
      upper lower cut hlower outside own) :=
  RightDecoder.law
    (slots clauses designated clean visible projected upper lower cut hlower outside own)
    rows upper lower W a repeats cut labeling
    (input clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a own) threshold

abbrev Seed := (own : OwnQuestions (t := t) (v := v) clean) →
  Answer clauses designated clean visible projected upper lower cut hlower outside own

def seedLaw : FiniteDistribution
    (Seed clauses designated clean visible projected upper lower cut hlower outside) :=
  FiniteProduct.law
    (kernel clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a labeling threshold)

theorem seedLaw_eval (own : OwnQuestions (t := t) (v := v) clean) :
    (seedLaw clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a labeling threshold).pushforward (fun seed => seed own) =
      kernel clauses designated clean visible projected upper lower cut hlower outside
        rows repeats record W a labeling threshold own :=
  FiniteProduct.eval_pushforward
    (kernel clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a labeling threshold) own

variable (hbranch : ∀ k < Nodes.height upper, 0 < branch k)

abbrev Form (own : OwnQuestions (t := t) (v := v) clean) :=
  RightDecoderDescendant.Form
    (slots clauses designated clean visible projected upper lower cut hlower outside own) lower

local instance formFintype (own : OwnQuestions (t := t) (v := v) clean) :
    Fintype (Form clauses designated clean visible projected upper lower cut hlower outside own) :=
  RightDecoderDescendant.formFintype
    (slots clauses designated clean visible projected upper lower cut hlower outside own) lower

def forms (seed : Seed clauses designated clean visible projected upper lower cut hlower outside)
    (own : OwnQuestions (t := t) (v := v) clean) :
    Form clauses designated clean visible projected upper lower cut hlower outside own :=
  RightDecoderDescendant.form
    (slots clauses designated clean visible projected upper lower cut hlower outside own)
    upper lower cut hbranch (seed own)

def formKernel (own : OwnQuestions (t := t) (v := v) clean) :
    FiniteDistribution (Form clauses designated clean visible projected
      upper lower cut hlower outside own) :=
  RightDecoderDescendant.formLaw
    (slots clauses designated clean visible projected upper lower cut hlower outside own)
    upper lower cut hbranch rows W a repeats labeling
    (input clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a own) threshold

theorem seedLaw_forms (own : OwnQuestions (t := t) (v := v) clean) :
    (seedLaw clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a labeling threshold).pushforward
        (fun seed => forms clauses designated clean visible projected upper lower cut hlower outside
          hbranch seed own) =
      formKernel clauses designated clean visible projected upper lower cut hlower outside
        rows repeats record W a labeling threshold hbranch own := by
  let decode := RightDecoderDescendant.form
    (slots clauses designated clean visible projected upper lower cut hlower outside own)
    upper lower cut hbranch
  change (seedLaw clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a labeling threshold).pushforward
        (fun seed => decode (seed own)) = _
  rw [← FiniteDistribution.pushforward_comp
    (seedLaw clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a labeling threshold)
    (fun seed : Seed clauses designated clean visible projected
      upper lower cut hlower outside => seed own) decode,
    seedLaw_eval clauses designated clean visible projected upper lower cut hlower outside
      rows repeats record W a labeling threshold own]
  rfl

end
end PerfectCompleteness.CleanRightDecoder

end

section

namespace PerfectCompleteness.CleanDecoderContext

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

abbrev F2 := ZMod 2

variable {branch : Nat → Nat} {n h : Nat}

theorem lowerHeight (upper : Nodes branch n)
    (d : HierarchicalFrozenTables.LowerNodes upper (h + 1)) :
    Nodes.height (HierarchicalLeftDecoder.LowerNode upper (h + 1) d) = h + 1 :=
  (RelativeDescendantProducts.relativeNode_height upper d.val.val).trans d.property

structure Exposed (branch rows repeats : Nat → Nat) (n h t v m : Nat) [NeZero m]
    (upper : Nodes branch n) (d : HierarchicalFrozenTables.LowerNodes upper (h + 1)) where
  clauses : Fin m → SourceClause.NormalizedClause v
  designated : Fin (branch h) → Slots branch h
  clean : Fin (branch h) → Prop
  visible : SourceQuestionReconstruction.Visible
    (E := SourceQuestionReconstruction.SourceTuple m t) designated clean
  projected : Fin (branch h) → Bool
  cleanProjected : ∀ i, clean i → projected i = true
  cut : OwnInputReference.Cut upper (HierarchicalLeftDecoder.LowerNode upper (h + 1) d)
  outside : Slots branch n → Fin t → MixedSupport.Slot
  leftTape : WholeCutReplay.Tape rows repeats
    (CleanRightDecoder.fullPath upper (HierarchicalLeftDecoder.LowerNode upper (h + 1) d)
      cut (lowerHeight upper d))
    (CutSlotAssembly.fill
      (CleanRightDecoder.fullPath upper (HierarchicalLeftDecoder.LowerNode upper (h + 1) d)
        cut (lowerHeight upper d)) outside
      (CleanEndpointSlots.leftReference clauses designated clean visible)) clean
  rightTape : CleanRightDecoder.Record clauses designated clean visible projected upper
    (HierarchicalLeftDecoder.LowerNode upper (h + 1) d) cut (lowerHeight upper d)
    outside rows repeats

variable {rows repeats : Nat → Nat} {t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (E : Exposed branch rows repeats n h t v m upper d)

abbrev lower (_E : Exposed branch rows repeats n h t v m upper d) :=
  HierarchicalLeftDecoder.LowerNode upper (h + 1) d

def path : Path branch n (h + 1) :=
  CleanRightDecoder.fullPath upper (lower E) E.cut (lowerHeight upper d)

abbrev CleanChildren := {i : Fin (branch h) // E.clean i}
abbrev LeftOwn := CleanChildren E → Fin t → Fin m
abbrev RightOwn := CleanChildren E → Fin t → Fin v

def leftExposed : CleanLeftDecoder.Exposed branch rows repeats n h t v m where
  clauses := E.clauses
  designated := E.designated
  clean := E.clean
  visible := E.visible
  path := path E
  outside := E.outside
  tape := E.leftTape

abbrev leftSlots (own : LeftOwn E) := CleanLeftDecoder.slots (leftExposed E) own
abbrev rightSlots (own : RightOwn E) :=
  CleanRightDecoder.slots E.clauses E.designated E.clean E.visible E.projected
    upper (lower E) E.cut (lowerHeight upper d) E.outside own

abbrev LeftSeed := CleanLeftDecoder.Seed (leftExposed E) upper
abbrev RightSeed := CleanRightDecoder.Seed E.clauses E.designated E.clean E.visible
  E.projected upper (lower E) E.cut (lowerHeight upper d) E.outside

variable (hbranch : ∀ k < n, 0 < branch k)

def leftOutput (seed : LeftSeed E) (own : LeftOwn E) :=
  CleanLeftDecoder.output (leftExposed E) upper (h + 1) hbranch d own (seed own)

def leftForm (seed : LeftSeed E) (own : LeftOwn E) :=
  CleanLeftDecoder.form (leftExposed E) upper (h + 1) hbranch d own (seed own)

def rightForm (seed : RightSeed E) (own : RightOwn E) :=
  CleanRightDecoder.forms E.clauses E.designated E.clean E.visible E.projected
    upper (lower E) E.cut (lowerHeight upper d) E.outside
    (DecoderSourcePullback.upperBranch upper hbranch) seed own

end
end PerfectCompleteness.CleanDecoderContext

end

end OAI
