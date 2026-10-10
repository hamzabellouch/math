import OAI.Computability.PerfectCompleteness.Construction.HierarchicalBucketFamily
import OAI.Computability.PerfectCompleteness.Decoding.FixedUpperPairErrorLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalUsefulBackground
import OAI.Computability.PerfectCompleteness.Sampling.CommonProductVariationLemmas
import OAI.Computability.PerfectCompleteness.Sampling.StoppedSourcePairLaw

namespace OAI

section

namespace PerfectCompleteness.FixedSourcePairVariation

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype
attribute [local instance 2000] HierarchicalUsefulCollision.backgroundFintype
  HierarchicalUsefulCollision.rowSpaceFintype

private theorem sigma_variation_le_const
    {O : Type*} [Fintype O] {R : O → Type*} [∀ o, Fintype (R o)]
    (outer : FiniteDistribution O)
    (P Q : (o : O) → FiniteDistribution (R o))
    (error : ℝ) (bound : ∀ o, (P o).totalVariation (Q o) ≤ error) :
    (CompletionSoundness.sigmaLaw outer P).totalVariation
      (CompletionSoundness.sigmaLaw outer Q) ≤ error := by
  rw [ConditionalVariation.sigma_totalVariation outer P Q]
  calc
    outer.expectation (fun o => (P o).totalVariation (Q o)) ≤
        outer.expectation (fun _ => error) :=
      SmallBias.expectation_mono outer bound
    _ = error := SmallBias.expectation_const outer error

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  {n i j v m : Nat}

abbrev Outer := StoppedProjectedExperiment.Outer
  (branch := FixedParameters.branch parameters) (n := n) (j := j)
  (t := FixedRows.sourceLength parameters.plan hδ) (m := m)

def flags : Fin (FixedParameters.branch parameters i) → FiniteDistribution Bool :=
  fun _ => ProjectionPosterior.bernoulli (FixedParameters.projectionProbability parameters i : ℝ)
    (by exact_mod_cast (FixedParameters.projectionProbability_bounds parameters i).1.le)
    (by exact_mod_cast (FixedParameters.projectionProbability_bounds parameters i).2.le)

abbrev positiveRows (height : Nat) : 0 < FixedRows.rows parameters.plan (height + 1) :=
  FixedUpperCutTriangle.rows_positive parameters (height + 1)

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (FixedParameters.branch parameters i) → Slots (FixedParameters.branch parameters) i)

abbrev experiment
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (FixedParameters.branch parameters) n
      (FixedRows.sourceLength parameters.plan hδ)))
    (o : Outer (n := n) (j := j) (m := m) parameters) :=
  StoppedProjectedBuckets.experiment clauses (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) hupper hij designated (positiveRows parameters) o
    (fun k _ => FixedParameters.branch_pos parameters k) (flags (i := i) parameters) σ

abbrev Descriptor (o : Outer (n := n) (j := j) (m := m) parameters) :=
  StoppedProjectedBuckets.Descriptor clauses (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) hupper hij designated (positiveRows parameters) o

def externalLaw (o : Outer (n := n) (j := j) (m := m) parameters) :
    FiniteDistribution (Descriptor parameters clauses hupper hij designated o) :=
  StoppedProjectedBuckets.externalLaw clauses (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) hupper hij designated (positiveRows parameters) o
    (fun k _ => FixedParameters.branch_pos parameters k) (flags (i := i) parameters)

abbrev background (o : Outer (n := n) (j := j) (m := m) parameters) :=
  StoppedProjectedBuckets.background clauses (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) hupper hij designated (positiveRows parameters) o

abbrev scalarLaw (o : Outer (n := n) (j := j) (m := m) parameters) :=
  StoppedProjectedBuckets.scalarLaw clauses (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) hupper hij designated (positiveRows parameters) o

abbrev upperRows (o : Outer (n := n) (j := j) (m := m) parameters) :=
  StoppedProjectedBuckets.rows_positive (FixedRows.rows parameters.plan) hupper (positiveRows parameters) o

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (FixedParameters.branch parameters) n
  (FixedRows.sourceLength parameters.plan hδ)))

local instance backgroundFintype (o : Outer (n := n) (j := j) (m := m) parameters) :
    Fintype (HierarchicalAgreementMean.Background (rows := FixedRows.rows parameters.plan)
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) := Fintype.ofFinite _

local instance rowSpaceFintype (o : Outer (n := n) (j := j) (m := m) parameters) :
    Fintype (NodeEmbedding.RowSpace (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) := Fintype.ofFinite _

abbrev PairFiber (o : Outer (n := n) (j := j) (m := m) parameters) :=
  HierarchicalAgreementMean.PairRecord (rows := FixedRows.rows parameters.plan)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (StoppedProjectedExperiment.upper hupper o)

abbrev PairRecord :=
  (o : Outer (n := n) (j := j) (m := m) parameters) × PairFiber parameters clauses hupper o

theorem fiber_lt_six (hroot : n ≤ parameters.plan.depth)
    (o : Outer (n := n) (j := j) (m := m) parameters) :
    (HierarchicalAdviceFromBuckets.pairedLaw (experiment parameters clauses hupper hij designated σ o)
      (externalLaw parameters clauses hupper hij designated o)
      (background parameters clauses hupper hij designated o)
      (scalarLaw parameters clauses hupper hij designated o) (upperRows parameters hupper o)).totalVariation
      (HierarchicalAgreementMean.referenceLaw
        (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)
        ((externalLaw parameters clauses hupper hij designated o).pushforward
          (background parameters clauses hupper hij designated o)) (upperRows parameters hupper o)) <
      6 * parameters.accuracy := by
  let pref := StoppedProjectedExperiment.upperPath hupper o
  let slots := StoppedProjectedExperiment.nativeSlots clauses o
  let projected := SourceProjectedWholeChoices.projected clauses hupper hij o
  let projection := SourceProjectedWholeChoices.projection clauses hupper hij o
  let choiceLaw := fun _ : UpperCutTriangle.Prefix (FixedParameters.branch parameters) j i =>
    SourceProjectedChoices.choiceLaw
      (branch := FixedParameters.branch parameters) (n := i)
      (t := FixedRows.sourceLength parameters.plan hδ)
  have hpair := StoppedSourcePairLaw.pairedLaw_eq_modified clauses
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan) hupper hij designated
    (positiveRows parameters) o (fun k _ => FixedParameters.branch_pos parameters k)
    (FixedParameters.projectionProbability parameters i : ℝ)
    (by exact_mod_cast (FixedParameters.projectionProbability_bounds parameters i).1.le)
    (by exact_mod_cast (FixedParameters.projectionProbability_bounds parameters i).2.le) σ
  change HierarchicalAdviceFromBuckets.pairedLaw
      (experiment parameters clauses hupper hij designated σ o)
      (externalLaw parameters clauses hupper hij designated o)
      (background parameters clauses hupper hij designated o)
      (scalarLaw parameters clauses hupper hij designated o) (upperRows parameters hupper o) =
    FixedUpperCutTriangle.modifiedPairLaw parameters pref (Nat.succ_le_succ hij.le) slots
      projected projection choiceLaw at hpair
  have h := FixedUpperCutTriangle.original_reference_lt parameters pref
    (Nat.succ_le_succ hij.le) slots projected projection choiceLaw hroot
  change (FixedUpperCutTriangle.modifiedPairLaw parameters pref (Nat.succ_le_succ hij.le) slots
      projected projection choiceLaw).totalVariation
    (HierarchicalAgreementMean.referenceLaw slots (upperNode pref)
      ((FixedUpperCutTriangle.modifiedPairLaw parameters pref (Nat.succ_le_succ hij.le) slots
        projected projection choiceLaw).pushforward Prod.fst) (upperRows parameters hupper o)) <
      6 * parameters.accuracy at h
  rw [← hpair] at h
  have hbackground :
      (HierarchicalAdviceFromBuckets.pairedLaw
        (experiment parameters clauses hupper hij designated σ o)
        (externalLaw parameters clauses hupper hij designated o)
        (background parameters clauses hupper hij designated o)
        (scalarLaw parameters clauses hupper hij designated o)
        (upperRows parameters hupper o)).pushforward Prod.fst =
      (externalLaw parameters clauses hupper hij designated o).pushforward
        (background parameters clauses hupper hij designated o) :=
    HierarchicalUsefulBackground.pairLaw_background slots (upperNode pref)
      (externalLaw parameters clauses hupper hij designated o)
      (background parameters clauses hupper hij designated o)
      (scalarLaw parameters clauses hupper hij designated o) (upperRows parameters hupper o)
  have hvariation := congrArg
    (fun backgroundLaw : FiniteDistribution
        (HierarchicalAgreementMean.Background (rows := FixedRows.rows parameters.plan)
          slots (upperNode pref)) =>
      (HierarchicalUsefulCollision.pairLaw slots (upperNode pref)
        (externalLaw parameters clauses hupper hij designated o)
        (background parameters clauses hupper hij designated o)
        (scalarLaw parameters clauses hupper hij designated o)
        (upperRows parameters hupper o)).totalVariation
        (HierarchicalAgreementMean.referenceLaw slots (upperNode pref)
          backgroundLaw (upperRows parameters hupper o))) hbackground
  exact lt_of_eq_of_lt hvariation.symm h

def actualLaw (outer : FiniteDistribution (Outer (n := n) (j := j) (m := m) parameters)) :
    FiniteDistribution (PairRecord parameters clauses hupper) :=
  HierarchicalBucketFamily.actualPairLaw (experiment parameters clauses hupper hij designated σ) outer
    (externalLaw parameters clauses hupper hij designated)
    (background parameters clauses hupper hij designated)
    (scalarLaw parameters clauses hupper hij designated) (upperRows parameters hupper)

def referenceLaw (outer : FiniteDistribution (Outer (n := n) (j := j) (m := m) parameters)) :
    FiniteDistribution (PairRecord parameters clauses hupper) :=
  HierarchicalBucketFamily.referencePairLaw (experiment parameters clauses hupper hij designated σ) outer
    (HierarchicalBucketFamily.actualBackgrounds (experiment parameters clauses hupper hij designated σ)
      (externalLaw parameters clauses hupper hij designated)
      (background parameters clauses hupper hij designated)) (upperRows parameters hupper)

theorem totalVariation_le_six (hroot : n ≤ parameters.plan.depth)
    (outer : FiniteDistribution (Outer (n := n) (j := j) (m := m) parameters)) :
    (actualLaw parameters clauses hupper hij designated σ outer).totalVariation
      (referenceLaw parameters clauses hupper hij designated σ outer) ≤ 6 * parameters.accuracy := by
  exact sigma_variation_le_const
    (R := PairFiber parameters clauses hupper) outer
    (fun o => HierarchicalAdviceFromBuckets.pairedLaw
      (experiment parameters clauses hupper hij designated σ o)
      (externalLaw parameters clauses hupper hij designated o)
      (background parameters clauses hupper hij designated o)
      (scalarLaw parameters clauses hupper hij designated o) (upperRows parameters hupper o))
    (fun o => HierarchicalAgreementMean.referenceLaw
      (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)
      ((externalLaw parameters clauses hupper hij designated o).pushforward
        (background parameters clauses hupper hij designated o)) (upperRows parameters hupper o))
    (6 * parameters.accuracy)
    (fun o => (fiber_lt_six parameters clauses hupper hij designated σ hroot o).le)

theorem totalVariation_le_ten (hroot : n ≤ parameters.plan.depth)
    (outer : FiniteDistribution (Outer (n := n) (j := j) (m := m) parameters)) :
    (actualLaw parameters clauses hupper hij designated σ outer).totalVariation
      (referenceLaw parameters clauses hupper hij designated σ outer) ≤ 10 * parameters.accuracy := by
  have h := totalVariation_le_six parameters clauses hupper hij designated σ hroot outer
  have hpositive := parameters.accuracy_pos
  linarith

end
end PerfectCompleteness.FixedSourcePairVariation

end

end OAI
