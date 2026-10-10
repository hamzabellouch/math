import OAI.Computability.PerfectCompleteness.Construction.HierarchicalBucketFamily
import OAI.Computability.PerfectCompleteness.Reduction.CanonicalGameLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedComparisonErrorsLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CandidateCoupling

namespace OAI


namespace PerfectCompleteness.HierarchicalFixedAdviceFamily

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)

theorem inverse_factor_eq_q (level : Nat) :
    ((inverse δ) ^ 2 / 4) /
        ((2 : ℝ) ^ (p.plan.order * FixedRows.rows p.plan level)) ^ 2 =
      q (inverse δ) p.plan.order (FixedRows.rows p.plan level) := by
  simp only [q, g, h, div_eq_mul_inv, pow_two]
  ring

theorem coarse_error_small (level : Nat) (hlevel : level ≤ p.plan.depth) :
    10 * p.accuracy ≤ p.plan.density *
      (((inverse δ) ^ 2 / 4) /
        ((2 : ℝ) ^ (p.plan.order * FixedRows.rows p.plan level)) ^ 2) / 16 := by
  rw [inverse_factor_eq_q p level]
  have hs := p.accuracy_small level hlevel
  simp only [CommonAccuracy.tolerance, lt_min_iff] at hs
  linarith [hs.2.2.1]

variable {branch : Nat → Nat} {t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment
    branch (FixedRows.rows p.plan) p.plan.depth t (Ω o))

local instance backgroundFiberFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)

local instance rowSpaceFintype (o : O) :
    Fintype (NodeEmbedding.RowSpace (S o).slots (S o).upper) := Fintype.ofFinite _

local instance inputFintype (z : HierarchicalAdviceFamily.Background S) :
    Fintype (HierarchicalAdviceFamily.Input S z) :=
  HierarchicalAdviceFamily.inputFintype S z

local instance inputFiniteDimensional (z : HierarchicalAdviceFamily.Background S) :
    FiniteDimensional F2 (HierarchicalAdviceFamily.Input S z) :=
  HierarchicalAdviceFamily.inputFiniteDimensional S z

local instance valueFintype (z : HierarchicalAdviceFamily.Background S) :
    Fintype (HierarchicalAdviceFamily.Value S z) :=
  HierarchicalAdviceFamily.valueFintype S z

local instance coarseFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Coarse (S o)) :=
  HierarchicalAdviceFamily.coarseFintype S o

omit [Fintype O] in
theorem rows_positive (o : O) :
    0 < FixedRows.rows p.plan (Nodes.height (S o).upper) :=
  HierarchicalFixedAdvice.rows_positive p (S o)

def predictionDifference (outer : FiniteDistribution O) : ℝ :=
  (HierarchicalAdviceFamily.originalLaw S outer p.plan.order).probability
      (HierarchicalAdviceFamily.prediction S (useful δ) p.plan.order p.plan.density) -
    rhoPred (useful δ) p.plan.density *
      (HierarchicalAdviceFamily.originalLaw S outer p.plan.order).probability
        (fun x => HierarchicalAdviceFamily.J S (useful δ) p.plan.order p.plan.density
          (HierarchicalAdviceFamily.observe S p.plan.order x))

variable {P : O → Type*} [∀ o, Fintype (P o)]
  (outer : FiniteDistribution O)
  (externalLaw : (o : O) → FiniteDistribution (P o))
  (background : (o : O) → P o → HierarchicalAdviceExperiment.Background (S o))
  (scalarLaw : (o : O) → P o →
    FiniteDistribution (NodeEmbedding.RowSpace (S o).slots (S o).upper))
  (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))

theorem mean_agreement_ge
    (hmass : simultaneous δ / 2 ≤ HierarchicalBucketFamily.usefulMass S (useful δ)
      outer externalLaw background scalarLaw (rows_positive p S))
    (hpaired : (HierarchicalBucketFamily.actualPairLaw S outer externalLaw background
      scalarLaw (rows_positive p S)).totalVariation
        (HierarchicalBucketFamily.referencePairLaw S outer backgrounds (rows_positive p S)) ≤
        10 * p.accuracy) :
    2 * inverse δ ≤ (HierarchicalAdviceFamily.backgroundLaw S outer backgrounds).expectation
      (fun z => PartialTableInverse.nonzeroAgreement (HierarchicalAdviceFamily.table S (useful δ) z)) := by
  calc
    2 * inverse δ = simultaneous δ ^ 2 / 16 := by unfold inverse; ring
    _ ≤ _ := HierarchicalBucketFamily.mean_agreement_ge S (useful δ) outer externalLaw
      background scalarLaw (rows_positive p S) backgrounds (simultaneous δ)
      (simultaneous_pos hδ).le hmass (hpaired.trans (HierarchicalFixedAdvice.paired_error_small p))

theorem prediction_difference (level : Nat) (hlevel : level ≤ p.plan.depth)
    (hheight : ∀ o, Nodes.height (S o).upper = level)
    (hmass : simultaneous δ / 2 ≤ HierarchicalBucketFamily.usefulMass S (useful δ)
      outer externalLaw background scalarLaw (rows_positive p S))
    (hpaired : (HierarchicalBucketFamily.actualPairLaw S outer externalLaw background
      scalarLaw (rows_positive p S)).totalVariation
        (HierarchicalBucketFamily.referencePairLaw S outer backgrounds (rows_positive p S)) ≤
        10 * p.accuracy)
    (hcoarse : ((HierarchicalAdviceFamily.originalLaw S outer p.plan.order).pushforward
      (HierarchicalAdviceFamily.observe S p.plan.order)).totalVariation
        ((HierarchicalAdviceFamily.referenceLaw S outer backgrounds p.plan.order).pushforward
          (HierarchicalAdviceFamily.referenceObserve S p.plan.order)) ≤ 10 * p.accuracy) :
    b (useful δ) p.plan.density (inverse δ) p.plan.order (FixedRows.rows p.plan level) ≤
      predictionDifference p S outer := by
  have hdim (o : O) :
      FixedRows.rows p.plan (Nodes.height (S o).upper) ≤ FixedRows.rows p.plan level := by
    rw [hheight o]
  have hbound := HierarchicalAdviceFamily.prediction_difference S (useful δ)
    (useful_pos hδ).le outer backgrounds (rows_positive p S)
    (FixedRows.rows p.plan level) hdim p.plan.order p.plan.density (inverse δ)
    (10 * p.accuracy) (inverse_pos hδ) p.plan.density_pos p.plan.density_lt p.plan.spectral
    (mean_agreement_ge p S outer externalLaw background scalarLaw backgrounds hmass hpaired)
    (by have := p.accuracy_pos; positivity) (coarse_error_small p level hlevel) hcoarse
  rw [inverse_factor_eq_q p level] at hbound
  have hfactor : useful δ * p.plan.density *
      q (inverse δ) p.plan.order (FixedRows.rows p.plan level) / 4 =
      b (useful δ) p.plan.density (inverse δ) p.plan.order (FixedRows.rows p.plan level) := by
    unfold b rhoPred
    ring
  rw [hfactor] at hbound
  exact hbound

end
end PerfectCompleteness.HierarchicalFixedAdviceFamily


namespace PerfectCompleteness.PreliminaryStrategy

open PreliminarySampler TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {v m n t : Nat} {branch rows repeats : Nat → Nat}

def observe (clauses : Fin m → SourceClause.NormalizedClause v)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (b : Base branch n t m)
    (arrays : Arrays (sourceSlots clauses (endpoints b.1)) rows)
    (choice : Choice rows b.2) : Bool :=
  let P := HierarchicalArrays.presentation clauses (endpoints b.1) rows arrays
  let slots := SourceKeys.slot clauses ∘ P.endpoints
  let projection := BlockQuotient.projectBlock
    (V := fun node : Nodes branch n => Block rows node) (B := PUnit.{1})
    (GeometricPath.nodeAtLevel b.2 choice.1) choice.2.val
  decide (CanonicalEdges.coarsen slots P.joint projection
      (KeyStrategy.label σ .left slots P.joint) =
    KeyStrategy.label σ .right slots (projection ∘ P.joint))

abbrev Strategy (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :=
  CompletionSoundness.LegalStrategy
    (HierarchicalGame.LeftLabel (family clauses branch n t rows repeats))
    (HierarchicalGame.RightLabel (family clauses branch n t rows repeats))

def extend (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat)
    (strategy : Strategy clauses branch n t rows repeats) :
    KeyStrategy.Strategy (TreeCanonical.locationCount branch n t) :=
  CanonicalGameStrategy.extend
    (HierarchicalGame.toBlockFamily (family clauses branch n t rows repeats)) strategy

theorem observe_extend_iff (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat)
    (strategy : Strategy clauses branch n t rows repeats)
    (e : Raw clauses branch n t rows repeats) :
    observe clauses (extend clauses branch n t rows repeats strategy) e.1
        (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
          (sourceSlots clauses (endpoints e.1.1)) e.2.1) e.2.2 = true ↔
      HierarchicalGame.edge (family clauses branch n t rows repeats) e
        (strategy.1 (HierarchicalGame.leftAt (family clauses branch n t rows repeats) e)) =
        strategy.2 (HierarchicalGame.rightAt (family clauses branch n t rows repeats) e) := by
  simp only [observe, decide_eq_true_eq]
  exact CanonicalGameStrategy.accepts_extend_iff
    (HierarchicalGame.toBlockFamily (family clauses branch n t rows repeats)) strategy e

theorem wins_eq_observe [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (strategy : Strategy clauses branch n t rows repeats)
    (e : Raw clauses branch n t rows repeats) :
    (game clauses branch n t rows repeats hn hbranch hrows).wins strategy e =
      observe clauses (extend clauses branch n t rows repeats strategy) e.1
        (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
          (sourceSlots clauses (endpoints e.1.1)) e.2.1) e.2.2 := by
  apply Bool.eq_iff_iff.mpr
  change @decide
    (HierarchicalGame.edge (family clauses branch n t rows repeats) e
      (strategy.1 (HierarchicalGame.leftAt (family clauses branch n t rows repeats) e)) =
        strategy.2 (HierarchicalGame.rightAt (family clauses branch n t rows repeats) e))
    (Classical.propDecidable _) = true ↔ _
  exact (@decide_eq_true_iff _ (Classical.propDecidable _)).trans
    (observe_extend_iff clauses branch n t rows repeats strategy e).symm

theorem success_eq_shared_candidate_mean [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (strategy : Strategy clauses branch n t rows repeats) :
    (game clauses branch n t rows repeats hn hbranch hrows).success strategy =
      (CandidateCoupling.sharedLaw clauses rows repeats hbranch hrows).expectation
        (fun e => CandidateCoupling.candidateFraction e.1.2
          (observe clauses (extend clauses branch n t rows repeats strategy) e.1 e.2.1) e.2.2) := by
  change (law clauses rows repeats hn hbranch hrows).probability
    ((game clauses branch n t rows repeats hn hbranch hrows).wins strategy) = _
  have hw : (game clauses branch n t rows repeats hn hbranch hrows).wins strategy =
      fun sample : Raw clauses branch n t rows repeats =>
        observe clauses (extend clauses branch n t rows repeats strategy) sample.1
          (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath sample.1.2)
            (sourceSlots clauses (endpoints sample.1.1)) sample.2.1) sample.2.2 :=
    funext (wins_eq_observe clauses branch n t rows repeats hn hbranch hrows strategy)
  rw [hw]
  exact CandidateCoupling.candidate_average_shared clauses rows repeats hn hbranch hrows
    (observe clauses (extend clauses branch n t rows repeats strategy))

end
end PerfectCompleteness.PreliminaryStrategy

end OAI
