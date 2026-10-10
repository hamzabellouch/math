import OAI.Computability.PerfectCompleteness.Construction.SourceChildKernelLemmas
import OAI.Computability.PerfectCompleteness.Decoding.CleanDecoderOddLists
import OAI.Computability.PerfectCompleteness.Decoding.CleanDecoderSeedLawLemmas
import OAI.Computability.PerfectCompleteness.Machines.CleanRecordDecoderInput
import OAI.Computability.PerfectCompleteness.Sampling.RecordSeedSamplingLemmas

namespace OAI

section

namespace PerfectCompleteness.CleanDecoderRate

noncomputable section

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

structure Setup (branch rows repeats : Nat → Nat) (n h t v m : Nat) [NeZero m]
    (upper : Nodes branch n) (d : HierarchicalFrozenTables.LowerNodes upper (h + 1)) where
  clauses : Fin m → SourceClause.NormalizedClause v
  designated : Fin (branch h) → Slots branch h
  cut : OwnInputReference.Cut upper (HierarchicalLeftDecoder.LowerNode upper (h + 1) d)
  outside : Slots branch n → Fin t → MixedSupport.Slot
  placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot
  exterior : CleanPhysicalReplay.Exterior rows repeats
    (CleanRecordDecoderInput.path upper d cut) outside placeholder

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : Setup branch rows repeats n h t v m upper d)

abbrev path := CleanRecordDecoderInput.path upper d S.cut
abbrev Calls := WholeCutCalls.Index rows repeats (path S)
abbrev Record := CleanRecordDecoderInput.Record (t := t) rows repeats upper d S.cut
  S.clauses S.designated
abbrev Sample := CleanRecordDecoderInput.Sample (t := t) rows repeats upper d S.cut
  S.clauses S.designated

def context (record : Record S) :=
  CleanRecordDecoderInput.exposed rows repeats upper d S.cut S.outside S.placeholder
    S.clauses S.designated record S.exterior

abbrev Seed (record : Record S) := CleanDecoderSeedLaw.Seed (context S record)

instance seedFintype (record : Record S) : Fintype (Seed S record) :=
  CleanDecoderSeedLaw.seedFintype (context S record)

abbrev observations (x : Sample S) : Record S :=
  CleanRecordDecoderInput.observe rows repeats upper d S.cut S.clauses S.designated x

abbrev sources (record : Record S) (x : Sample S) :=
  CleanRecordDecoderInput.sources rows repeats upper d S.cut S.clauses S.designated record x

def rawLaw (cube : Nat) (hcube : 0 < cube) : FiniteDistribution (Sample S) :=
  SourceChildKernel.originalLaw (C := Calls S) (t := t) rows S.clauses S.designated
    (fun _ => ProjectedCleanRate.projectionFlag cube hcube)

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (record : Record S) →
    CleanLeftDecoder.Useful (CleanDecoderContext.leftExposed (context S record)) upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
  (a : OwnInputReference.LowerVector rows (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))
  (threshold : ℝ)

def kernel (record : Record S) : FiniteDistribution (Seed S record) :=
  CleanDecoderSeedLaw.seedLaw (context S record) σ (useful record) r ρ A W a threshold

def law (cube : Nat) (hcube : 0 < cube) :
    FiniteDistribution (Σ x : Sample S, Seed S (observations S x)) :=
  RecordSeedSampling.freshLaw (rawLaw S cube hcube) (observations S)
    (kernel S σ useful r ρ A W a threshold)

variable (hbranch : ∀ k < n, 0 < branch k)

def agrees (s : Nat) (x : Sample S) (seed : Seed S (observations S x)) : Bool :=
  decide
    (OddListExtraction.formRank
      (H (CleanDecoderOddLists.leftNative (context S (observations S x))
        (CleanDecoderOddLists.leftQuestions (context S (observations S x))
          (sources S (observations S x) x))))
      (CleanDecoderContext.leftForm (context S (observations S x)) hbranch seed.1
        (CleanDecoderOddLists.leftQuestions (context S (observations S x))
          (sources S (observations S x) x))) ≤ s ∧
    seed.2 (CleanDecoderOddLists.rightQuestions (context S (observations S x))
      (sources S (observations S x) x)) =
      CleanDecoderOddLists.target (context S (observations S x)) seed.1
        (sources S (observations S x) x))

theorem bound {s L cube : Nat} [NeZero s] (hcube : 0 < cube) (hρ : 0 < ρ)
    (repetition : ∀ k, ((SourceOddLists.game s S.clauses t).repetition k).value ≤
      (RepetitionRate.halfRate L : ℝ) ^ k) :
    (law S σ useful r ρ A W a threshold cube hcube).probability
        (fun z => agrees S hbranch s z.1 z.2) ≤
      (1 - ProjectedCleanRate.coefficient L branch h t (Fintype.card (Calls S)) rows /
        (cube : ℝ) ^ 2) ^ (branch h) := by
  unfold law
  apply RecordSeedSampling.probability_le_of_supported_tables
  intro table htable
  let strategies := fun record : Record S =>
    CleanDecoderOddLists.strategy (context S record) hbranch (Nat.pos_of_neZero s)
      (table record).1 (table record).2
  apply SourceChildKernelRate.bound_from_repetition rows S.clauses S.designated
    hcube repetition _ strategies
  intro record x hevent heventSeed
  have hrecord : observations S x = record := by
    apply of_decide_eq_true
    exact (CleanRecordObservation.event_eq rows S.clauses S.designated record x).symm.trans hevent
  subst record
  have hseed := RecordSeedSampling.supported_row
    (kernel S σ useful r ρ A W a threshold) table htable (observations S x)
  have hleft := CleanDecoderSeedLaw.supported_left (context S (observations S x))
    σ (useful (observations S x)) r ρ A W a threshold
    (table (observations S x)) hseed
  have hagrees : agrees S hbranch s x (table (observations S x)) = true :=
    (Bool.and_eq_true_iff.mp heventSeed).2
  have hactual := of_decide_eq_true hagrees
  simp only [OccurrenceGame.wins, IndexedRepetition.game, SourceOddLists.game,
    OddListGame.game, OccurrenceGame.ofProjection, strategies,
    CleanDecoderOddLists.strategy, decide_eq_true_eq]
  intro i
  exact CleanDecoderOddLists.responses_accept (context S (observations S x)) hbranch
    σ (useful (observations S x)) (Nat.pos_of_neZero s) r ρ hρ A
    (table (observations S x)).1 hleft (table (observations S x)).2
    (sources S (observations S x) x) hactual.2 hactual.1 i

theorem amplified_bound {s L cube : Nat} [NeZero s]
    (γ : ℚ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (ht : t = SourceOddLists.repetitionLength γ s hγ hγ1)
    (hcube : 0 < cube) (hρ : 0 < ρ)
    (gap : SourceAmplification.ClauseGap S.clauses γ)
    (hL : 0 < L) (alphabet : SourceOddLists.alphabetLog s t ≤ L) :
    (law S σ useful r ρ A W a threshold cube hcube).probability
        (fun z => agrees S hbranch s z.1 z.2) ≤
      (1 - ProjectedCleanRate.coefficient L branch h t (Fintype.card (Calls S)) rows /
        (cube : ℝ) ^ 2) ^ (branch h) := by
  apply bound S σ useful r ρ A W a threshold hbranch hcube hρ
  subst t
  exact SourceOddLists.repetition_halfRate S.clauses γ hγ hγ1 gap hL alphabet

end
end PerfectCompleteness.CleanDecoderRate

end

section

namespace PerfectCompleteness.CleanDecoderPairLaw

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

abbrev context (x : CleanDecoderRate.Sample S) :=
  CleanDecoderRate.context S (CleanDecoderRate.observations S x)

abbrev occurrences (x : CleanDecoderRate.Sample S) :=
  CleanDecoderRate.sources S (CleanDecoderRate.observations S x) x

abbrev leftOwn (x : CleanDecoderRate.Sample S) :=
  CleanDecoderOddLists.leftQuestions (context S x) (occurrences S x)

abbrev rightOwn (x : CleanDecoderRate.Sample S) :=
  CleanDecoderOddLists.rightQuestions (context S x) (occurrences S x)

abbrev LeftAnswer (x : CleanDecoderRate.Sample S) :=
  CleanDecoderSeedLaw.LeftAnswer (context S x) (leftOwn S x)

abbrev RightAnswer (x : CleanDecoderRate.Sample S) :=
  CleanDecoderSeedLaw.RightAnswer (context S x) (rightOwn S x)

instance leftAnswerFintype (x : CleanDecoderRate.Sample S) : Fintype (LeftAnswer S x) :=
  CleanLeftDecoder.upperAnswerFintype
    (CleanDecoderContext.leftExposed (context S x)) upper (leftOwn S x)

instance rightAnswerFintype (x : CleanDecoderRate.Sample S) : Fintype (RightAnswer S x) :=
  RightDecoder.scalarFintype (CleanDecoderContext.rightSlots (context S x) (rightOwn S x)) upper

abbrev Pair (x : CleanDecoderRate.Sample S) := LeftAnswer S x × RightAnswer S x

instance pairFintype (x : CleanDecoderRate.Sample S) : Fintype (Pair S x) :=
  inferInstanceAs (Fintype (LeftAnswer S x × RightAnswer S x))

def read (x : CleanDecoderRate.Sample S)
    (seed : CleanDecoderRate.Seed S (CleanDecoderRate.observations S x)) : Pair S x :=
  (seed.1 (leftOwn S x), seed.2 (rightOwn S x))

def readSample
    (z : Σ x : CleanDecoderRate.Sample S, CleanDecoderRate.Seed S (CleanDecoderRate.observations S x)) :
    Σ x : CleanDecoderRate.Sample S, Pair S x :=
  ⟨z.1, read S z.1 z.2⟩

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (record : CleanDecoderRate.Record S) →
    CleanLeftDecoder.Useful (CleanDecoderContext.leftExposed (CleanDecoderRate.context S record))
      upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
  (a : OwnInputReference.LowerVector rows (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))
  (threshold : ℝ)

def pairKernel (x : CleanDecoderRate.Sample S) : FiniteDistribution (Pair S x) :=
  (CleanDecoderSeedLaw.leftKernel (context S x) σ (useful (CleanDecoderRate.observations S x))
    r ρ A (leftOwn S x)).product
      (CleanDecoderSeedLaw.rightKernel (context S x) σ W a threshold (rightOwn S x))

def pairLaw (cube : Nat) (hcube : 0 < cube) :
    FiniteDistribution (Σ x : CleanDecoderRate.Sample S, Pair S x) :=
  CompletionSoundness.sigmaLaw (CleanDecoderRate.rawLaw S cube hcube)
    (pairKernel S σ useful r ρ A W a threshold)

theorem read_law (x : CleanDecoderRate.Sample S) :
    (CleanDecoderRate.kernel S σ useful r ρ A W a threshold
      (CleanDecoderRate.observations S x)).pushforward (read S x) =
        pairKernel S σ useful r ρ A W a threshold x :=
  CleanDecoderSeedLaw.read_law (context S x) σ (useful (CleanDecoderRate.observations S x))
    r ρ A W a threshold (leftOwn S x) (rightOwn S x)

theorem probability_read (cube : Nat) (hcube : 0 < cube)
    (event : (x : CleanDecoderRate.Sample S) → Pair S x → Bool) :
    (pairLaw S σ useful r ρ A W a threshold cube hcube).probability
      (fun z => event z.1 z.2) =
    (CleanDecoderRate.law S σ useful r ρ A W a threshold cube hcube).probability
      (fun z => event z.1 (read S z.1 z.2)) := by
  rw [pairLaw, CleanDecoderRate.law, RecordSeedSampling.freshLaw,
    CompletionSoundness.sigmaLaw_probability, CompletionSoundness.sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro x
  exact (CleanDecoderSeedLaw.probability_read (context S x) σ
    (useful (CleanDecoderRate.observations S x)) r ρ A W a threshold
    (leftOwn S x) (rightOwn S x) (fun left right => event x (left, right))).symm

theorem law_pushforward (cube : Nat) (hcube : 0 < cube) :
    (CleanDecoderRate.law S σ useful r ρ A W a threshold cube hcube).pushforward (readSample S) =
      pairLaw S σ useful r ρ A W a threshold cube hcube := by
  apply FiniteDistribution.eq_of_weight_eq
  intro answer
  rw [FiniteDistribution.weight_eq_probability_singleton,
    FiniteDistribution.weight_eq_probability_singleton, FiniteDistribution.probability_pushforward]
  have readProbability := probability_read S σ useful r ρ A W a threshold cube hcube
    (fun sample pair =>
      decide ((⟨sample, pair⟩ : Σ x : CleanDecoderRate.Sample S, Pair S x) = answer))
  simp only [Sigma.eta] at readProbability
  convert readProbability.symm using 1
  congr 1

variable (hbranch : ∀ k < n, 0 < branch k)

def pairAgrees (s : Nat) (x : CleanDecoderRate.Sample S) (answer : Pair S x) : Bool :=
  decide
    (OddListExtraction.formRank
      (H (CleanDecoderOddLists.leftNative (context S x) (leftOwn S x)))
      (CleanLeftDecoder.form (CleanDecoderContext.leftExposed (context S x)) upper (h + 1)
        hbranch d (leftOwn S x) answer.1) ≤ s ∧
    answer.2 = DecoderSourcePullback.upperTarget
      (CleanDecoderOddLists.fullProjection (context S x) (occurrences S x)) upper answer.1)

@[simp] theorem pairAgrees_read (s : Nat) (x : CleanDecoderRate.Sample S)
    (seed : CleanDecoderRate.Seed S (CleanDecoderRate.observations S x)) :
    pairAgrees S hbranch s x (read S x seed) = CleanDecoderRate.agrees S hbranch s x seed := rfl

theorem pair_probability_eq (s cube : Nat) (hcube : 0 < cube) :
    (pairLaw S σ useful r ρ A W a threshold cube hcube).probability
      (fun z => pairAgrees S hbranch s z.1 z.2) =
    (CleanDecoderRate.law S σ useful r ρ A W a threshold cube hcube).probability
      (fun z => CleanDecoderRate.agrees S hbranch s z.1 z.2) := by
  exact probability_read S σ useful r ρ A W a threshold cube hcube (pairAgrees S hbranch s)

theorem bound {s L cube : Nat} [NeZero s] (hcube : 0 < cube) (hρ : 0 < ρ)
    (repetition : ∀ k, ((SourceOddLists.game s S.clauses t).repetition k).value ≤
      (RepetitionRate.halfRate L : ℝ) ^ k) :
    (pairLaw S σ useful r ρ A W a threshold cube hcube).probability
      (fun z => pairAgrees S hbranch s z.1 z.2) ≤
      (1 - ProjectedCleanRate.coefficient L branch h t
        (Fintype.card (CleanDecoderRate.Calls S)) rows / (cube : ℝ) ^ 2) ^ (branch h) := by
  rw [pair_probability_eq]
  exact CleanDecoderRate.bound S σ useful r ρ A W a threshold hbranch hcube hρ repetition

theorem amplified_bound {s L cube : Nat} [NeZero s]
    (γ : ℚ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (ht : t = SourceOddLists.repetitionLength γ s hγ hγ1)
    (hcube : 0 < cube) (hρ : 0 < ρ)
    (gap : SourceAmplification.ClauseGap S.clauses γ)
    (hL : 0 < L) (alphabet : SourceOddLists.alphabetLog s t ≤ L) :
    (pairLaw S σ useful r ρ A W a threshold cube hcube).probability
      (fun z => pairAgrees S hbranch s z.1 z.2) ≤
      (1 - ProjectedCleanRate.coefficient L branch h t
        (Fintype.card (CleanDecoderRate.Calls S)) rows / (cube : ℝ) ^ 2) ^ (branch h) := by
  rw [pair_probability_eq]
  exact CleanDecoderRate.amplified_bound S σ useful r ρ A W a threshold hbranch
    γ hγ hγ1 ht hcube hρ gap hL alphabet

end
end PerfectCompleteness.CleanDecoderPairLaw

end

end OAI
