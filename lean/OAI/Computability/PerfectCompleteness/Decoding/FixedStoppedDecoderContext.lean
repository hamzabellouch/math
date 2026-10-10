import OAI.Computability.PerfectCompleteness.Decoding.DecoderFamilyLawLemmas
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalDirections
import OAI.Computability.PerfectCompleteness.Foundations.GeometricPrefixSplit
import OAI.Computability.PerfectCompleteness.Repetition.StoppedCleanGeometry

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedDecoderContext

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j)

abbrev Prefixes :=
  GeometricCutSplit.Prefix (FixedParameters.branch parameters) parameters.plan.depth (j.val + 1) ×
    GeometricCutSplit.Prefix (FixedParameters.branch parameters) (j.val + 1) (i.val + 1)

def upperPath (pref : Prefixes parameters i j) :
    Path (FixedParameters.branch parameters) parameters.plan.depth (j.val + 1) :=
  GeometricCutSplit.prefixPath (Nat.succ_le_of_lt j.isLt) pref.1

def lowerPath (pref : Prefixes parameters i j) :
    Path (FixedParameters.branch parameters) (j.val + 1) (i.val + 1) :=
  GeometricCutSplit.prefixPath (Nat.succ_le_succ (Nat.le_of_lt hij)) pref.2

def upper (pref : Prefixes parameters i j) : Nodes (FixedParameters.branch parameters) parameters.plan.depth :=
  WholeArrayInteriorExterior.upperNode (upperPath parameters i j pref)

def lower (pref : Prefixes parameters i j) :
    HierarchicalFrozenTables.LowerNodes (upper parameters i j pref) (i.val + 1) :=
  StoppedCleanGeometry.descendant (upperPath parameters i j pref)
    (lowerPath parameters i j hij pref) hij

@[simp] theorem upper_height (pref : Prefixes parameters i j) :
    Nodes.height (upper parameters i j pref) = j.val + 1 :=
  WholeArrayInteriorExterior.upperNode_height _

def prefixLaw : FiniteDistribution (Prefixes parameters i j) :=
  (GeometricCutSplit.prefixLaw (Nat.succ_le_of_lt j.isLt)
    (fun k _ => FixedParameters.branch_pos parameters k)).product
      (GeometricCutSplit.prefixLaw (Nat.succ_le_succ (Nat.le_of_lt hij))
        (fun k _ => FixedParameters.branch_pos parameters k))

variable (input : List Bool)

abbrev OutsideQuestions (pref : Prefixes parameters i j) :=
  StoppedCleanGeometry.OutsideQuestions parameters input
    (upperPath parameters i j pref) (lowerPath parameters i j hij pref)

abbrev Exterior (pref : Prefixes parameters i j)
    (external : OutsideQuestions parameters i j hij input pref) :=
  StoppedCleanGeometry.Exterior parameters input
    (upperPath parameters i j pref) (lowerPath parameters i j hij pref) external

abbrev Advice (pref : Prefixes parameters i j) :=
  ManyGoodRows.RowMap (Block (FixedRows.rows parameters.plan) (upper parameters i j pref))
    parameters.plan.order

abbrev Directions := CanonicalDirections.Tuple (FixedRows.rows parameters.plan) parameters.plan.depth

abbrev Fiber (pref : Prefixes parameters i j)
    (external : OutsideQuestions parameters i j hij input pref) :=
  Advice parameters i j pref ×
    (Directions parameters × Exterior parameters i j hij input pref external)

abbrev Context :=
  (pref : Prefixes parameters i j) ×
    (external : OutsideQuestions parameters i j hij input pref) ×
      Fiber parameters i j hij input pref external

def directionLaw : FiniteDistribution (Directions parameters) :=
  CanonicalDirections.law (FixedRows.rows parameters.plan) parameters.plan.depth
    (fun k => parameters.plan.rows_pos (parameters.plan.depth - (k + 1)))

def fiberLaw (pref : Prefixes parameters i j)
    (external : OutsideQuestions parameters i j hij input pref) :
    FiniteDistribution (Fiber parameters i j hij input pref external) :=
  (FiniteDistribution.uniform (Advice parameters i j pref)).product
    ((directionLaw parameters).product
      (FiniteDistribution.uniform (Exterior parameters i j hij input pref external)))

def law : FiniteDistribution (Context parameters i j hij input) :=
  CompletionSoundness.sigmaLaw (prefixLaw parameters i j hij) (fun pref =>
    CompletionSoundness.sigmaLaw
      (FiniteDistribution.uniform (OutsideQuestions parameters i j hij input pref))
      (fiberLaw parameters i j hij input pref))

def upperNode (context : Context parameters i j hij input) := upper parameters i j context.1

def lowerIndex (context : Context parameters i j hij input) := lower parameters i j hij context.1

def geometry (context : Context parameters i j hij input) :
    FixedDecoderCleanRate.Geometry parameters parameters.plan.depth i.val
      (upperNode parameters i j hij input context) (lowerIndex parameters i j hij input context) :=
  StoppedCleanGeometry.geometry parameters input
    (upperPath parameters i j context.1) (lowerPath parameters i j hij context.1) hij
    context.2.1 context.2.2.2.2

def advice (context : Context parameters i j hij input) :
    ManyGoodRows.RowMap
      (Block (FixedRows.rows parameters.plan) (upperNode parameters i j hij input context))
      parameters.plan.order := context.2.2.1

def direction (context : Context parameters i j hij input) :
    OwnInputReference.LowerVector (FixedRows.rows parameters.plan)
      (HierarchicalLeftDecoder.LowerNode (upperNode parameters i j hij input context)
        (i.val + 1) (lowerIndex parameters i j hij input context)) :=
  (PrefixTests.nodeDirection (FixedRows.rows parameters.plan) i
    ⟨HierarchicalLeftDecoder.LowerNode (upperNode parameters i j hij input context)
      (i.val + 1) (lowerIndex parameters i j hij input context),
      CleanDecoderContext.lowerHeight (upperNode parameters i j hij input context)
        (lowerIndex parameters i j hij input context)⟩ (context.2.2.2.1 i)).val

theorem row_count (context : Context parameters i j hij input) :
    FixedRows.rows parameters.plan (Nodes.height (upperNode parameters i j hij input context)) =
      FixedRows.rows parameters.plan (j.val + 1) := by
  rw [upperNode, upper_height]

theorem advice_marginal (pref : Prefixes parameters i j)
    (external : OutsideQuestions parameters i j hij input pref) :
    (fiberLaw parameters i j hij input pref external).pushforward Prod.fst =
      FiniteDistribution.uniform (Advice parameters i j pref) :=
  HiddenBucketBias.product_fst _ _

end
end PerfectCompleteness.FixedStoppedDecoderContext

end

end OAI
