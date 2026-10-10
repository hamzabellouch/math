import OAI.Computability.PerfectCompleteness.Decoding.DecoderFamilyLawLemmas
import OAI.Computability.PerfectCompleteness.Decoding.FixedStoppedDecoderContext
import OAI.Computability.PerfectCompleteness.Foundations.SlotProjectedExperiment
import OAI.Computability.PerfectCompleteness.Reduction.FixedPhysicalStoppedComparison
import OAI.Computability.PerfectCompleteness.Reduction.PreliminaryOutputLemmas

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedDecoderLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

private abbrev familySampleFintype
    {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
    {O : Type*} [Fintype O]
    {upper : O → Nodes branch n}
    {lower : (o : O) → HierarchicalFrozenTables.LowerNodes (upper o) (h + 1)}
    (S : (o : O) → CleanDecoderRate.Setup branch rows repeats n h t v m (upper o) (lower o)) :
    Fintype (DecoderFamilyLaw.Sample S) := inferInstance

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

abbrev Context := FixedStoppedDecoderContext.Context parameters i j hij input

def labeling (strategy : FixedPreliminaryGame.Strategy parameters input) :
    KeyStrategy.Strategy (TreeCanonical.locationCount (FixedParameters.branch parameters)
      parameters.plan.depth (FixedRows.sourceLength parameters.plan hδ)) :=
  PreliminaryStrategy.extend (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (FixedParameters.branch parameters) parameters.plan.depth
    (FixedRows.sourceLength parameters.plan hδ) (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) strategy

def flag : Fin (FixedParameters.branch parameters i.val) → FiniteDistribution Bool :=
  fun _ => ProjectionPosterior.bernoulli
    (FixedParameters.projectionProbability parameters i.val : ℝ)
    (FixedPhysicalStoppedComparison.beta_nonneg parameters)
    (FixedPhysicalStoppedComparison.beta_le_one parameters)

def markFamily (strategy : FixedPreliminaryGame.Strategy parameters input)
    (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :=
  SlotProjectedExperiment.family
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij pref.1
    (fun k _ => FixedParameters.branch_pos parameters k)
    (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1))
    (flag parameters i) (labeling parameters input strategy)

abbrev setups :=
  FixedDecoderFamilyRate.setups parameters
    (FixedStoppedDecoderContext.geometry parameters i j hij input) input

def useful (strategy : FixedPreliminaryGame.Strategy parameters input)
    (context : Context parameters i j hij input)
    (record : CleanDecoderRate.Record (setups parameters i j hij input context)) :
    CleanLeftDecoder.Useful
      (CleanDecoderContext.leftExposed
        (CleanDecoderRate.context (setups parameters i j hij input context) record))
      (FixedStoppedDecoderContext.upperNode parameters i j hij input context) (i.val + 1) :=
  OriginalDecoderMark.useful
    (markFamily parameters i j hij input strategy context.1)
    (FixedStoppedDecoderContext.upperNode parameters i j hij input context) (i.val + 1)
    (InitialParameters.useful δ)
    (CleanDecoderContext.leftExposed
      (CleanDecoderRate.context (setups parameters i j hij input context) record))

def threshold : ℝ :=
  UpperParameterScalars.tau (InitialParameters.useful δ) parameters.plan.density
    parameters.plan.order (FixedRows.rows parameters.plan (j.val + 1))

abbrev Sample := DecoderFamilyLaw.Sample (setups parameters i j hij input)

local instance sampleFintype : Fintype (Sample parameters i j hij input) :=
  familySampleFintype (setups parameters i j hij input)

def law (strategy : FixedPreliminaryGame.Strategy parameters input) :
    FiniteDistribution (Sample parameters i j hij input) :=
  DecoderFamilyLaw.law (setups parameters i j hij input)
    (labeling parameters input strategy) (useful parameters i j hij input strategy)
    parameters.plan.order parameters.plan.density
    (FixedStoppedDecoderContext.advice parameters i j hij input) (FixedStoppedDecoderContext.direction parameters i j hij input)
    (threshold parameters j) (FixedStoppedDecoderContext.law parameters i j hij input)
    (parameters.cubeSize i.val) (FixedDecoderCleanRate.cubePositive parameters i.val)

abbrev meeting : Sample parameters i j hij input → Bool :=
  DecoderFamilyLaw.meeting (setups parameters i j hij input)

abbrev lowAgreement : Sample parameters i j hij input → Bool :=
  DecoderFamilyLaw.lowAgreement (setups parameters i j hij input)
    (FixedDecoderCleanRate.branchPositive parameters)
    (FixedRows.cutoff parameters.plan hδ)

abbrev highAgreement : Sample parameters i j hij input → Bool :=
  DecoderFamilyLaw.highAgreement (setups parameters i j hij input)
    (FixedDecoderCleanRate.branchPositive parameters)
    (FixedRows.cutoff parameters.plan hδ)

theorem probability_split (strategy : FixedPreliminaryGame.Strategy parameters input) :
    (law parameters i j hij input strategy).probability (meeting parameters i j hij input) =
      (law parameters i j hij input strategy).probability
        (lowAgreement parameters i j hij input) +
      (law parameters i j hij input strategy).probability
        (highAgreement parameters i j hij input) :=
  DecoderFamilyLaw.probability_split (setups parameters i j hij input)
    (FixedDecoderCleanRate.branchPositive parameters)
    (labeling parameters input strategy) (useful parameters i j hij input strategy)
    parameters.plan.order parameters.plan.density
    (FixedStoppedDecoderContext.advice parameters i j hij input) (FixedStoppedDecoderContext.direction parameters i j hij input)
    (threshold parameters j) (FixedStoppedDecoderContext.law parameters i j hij input)
    (FixedRows.cutoff parameters.plan hδ) (parameters.cubeSize i.val)
    (FixedDecoderCleanRate.cubePositive parameters i.val)

theorem low_probability_lt_accuracy
    (strategy : FixedPreliminaryGame.Strategy parameters input)
    (unsat : ¬ BinaryLanguage.language input) :
    (law parameters i j hij input strategy).probability
      (lowAgreement parameters i j hij input) < parameters.accuracy :=
  FixedDecoderFamilyRate.probability_lt_accuracy parameters
    (FixedStoppedDecoderContext.geometry parameters i j hij input) input
    (labeling parameters input strategy) (useful parameters i j hij input strategy)
    parameters.plan.order parameters.plan.density
    (FixedStoppedDecoderContext.advice parameters i j hij input) (FixedStoppedDecoderContext.direction parameters i j hij input)
    (threshold parameters j) (FixedStoppedDecoderContext.law parameters i j hij input)
    unsat (le_refl _) parameters.plan.density_pos

end
end PerfectCompleteness.FixedStoppedDecoderLaw

end

end OAI
