import OAI.Computability.PerfectCompleteness.Algebra.DecoderRankSplit
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedFiberSquare

namespace OAI

section

namespace PerfectCompleteness.DecoderFamilyLaw

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {O : Type*} [Fintype O]
  {upper : O → Nodes branch n}
  {lower : (o : O) → HierarchicalFrozenTables.LowerNodes (upper o) (h + 1)}
  (S : (o : O) → CleanDecoderRate.Setup branch rows repeats n h t v m (upper o) (lower o))

abbrev Fiber (o : O) :=
  Σ x : CleanDecoderRate.Sample (S o), CleanDecoderPairLaw.Pair (S o) x

abbrev Sample := Σ o : O, Fiber S o

def meeting (z : Sample S) : Bool :=
  DecoderRankSplit.meeting (S z.1) z.2.1 z.2.2

variable (hbranch : ∀ k < n, 0 < branch k)

def lowAgreement (s : Nat) (z : Sample S) : Bool :=
  CleanDecoderPairLaw.pairAgrees (S z.1) hbranch s z.2.1 z.2.2

def highAgreement (s : Nat) (z : Sample S) : Bool :=
  DecoderRankSplit.highAgrees (S z.1) hbranch s z.2.1 z.2.2

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (o : O) → (record : CleanDecoderRate.Record (S o)) →
    CleanLeftDecoder.Useful
      (CleanDecoderContext.leftExposed (CleanDecoderRate.context (S o) record))
      (upper o) (h + 1))
  (r : Nat) (ρ : ℝ)
  (A : (o : O) → ManyGoodRows.RowMap (Block rows (upper o)) r)
  (a : (o : O) → OwnInputReference.LowerVector rows
    (HierarchicalLeftDecoder.LowerNode (upper o) (h + 1) (lower o)))
  (threshold : ℝ)

def fiberLaw (cube : Nat) (hcube : 0 < cube) (o : O) :
    FiniteDistribution (Fiber S o) :=
  CleanDecoderPairLaw.pairLaw (S o) σ (useful o) r ρ (A o)
    (LinearMap.ker (A o)) (a o) threshold cube hcube

def law (outer : FiniteDistribution O) (cube : Nat) (hcube : 0 < cube) :
    FiniteDistribution (Sample S) :=
  CompletionSoundness.sigmaLaw outer
    (fiberLaw S σ useful r ρ A a threshold cube hcube)

theorem probability_eq_expectation
    (outer : FiniteDistribution O) (cube : Nat) (hcube : 0 < cube)
    (event : Sample S → Bool) :
    (law S σ useful r ρ A a threshold outer cube hcube).probability event =
      outer.expectation (fun o =>
        (fiberLaw S σ useful r ρ A a threshold cube hcube o).probability
          (fun x => event ⟨o, x⟩)) := by
  exact CompletionSoundness.sigmaLaw_probability outer
    (fiberLaw S σ useful r ρ A a threshold cube hcube) event

theorem probability_split
    (outer : FiniteDistribution O) (s cube : Nat) (hcube : 0 < cube) :
    (law S σ useful r ρ A a threshold outer cube hcube).probability (meeting S) =
      (law S σ useful r ρ A a threshold outer cube hcube).probability
        (lowAgreement S hbranch s) +
      (law S σ useful r ρ A a threshold outer cube hcube).probability
        (highAgreement S hbranch s) := by
  rw [probability_eq_expectation, probability_eq_expectation,
    probability_eq_expectation]
  have heq := FiniteDistribution.expectation_congr outer
    (fun o => DecoderRankSplit.pair_probability_split (S o) hbranch σ (useful o)
      r ρ (A o) (LinearMap.ker (A o)) (a o) threshold s cube hcube)
  simpa only [FiniteDistribution.expectation, mul_add, Finset.sum_add_distrib,
    meeting, lowAgreement, highAgreement, fiberLaw] using heq

theorem meeting_probability_ge
    (outer : FiniteDistribution O) (cube : Nat) (hcube : 0 < cube)
    (bound : O → ℝ)
    (hbound : ∀ o, bound o ≤
      (fiberLaw S σ useful r ρ A a threshold cube hcube o).probability
        (fun x => DecoderRankSplit.meeting (S o) x.1 x.2)) :
    outer.expectation bound ≤
      (law S σ useful r ρ A a threshold outer cube hcube).probability (meeting S) := by
  rw [probability_eq_expectation]
  exact SmallBias.expectation_mono outer hbound

end
end PerfectCompleteness.DecoderFamilyLaw

end

section

namespace PerfectCompleteness.DecoderPairHighOutput

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

abbrev exposed (x : CleanDecoderRate.Sample S) :=
  CleanDecoderContext.leftExposed (CleanDecoderPairLaw.context S x)

abbrev slots (x : CleanDecoderRate.Sample S) :=
  CleanLeftDecoder.slots (exposed S x) (CleanDecoderPairLaw.leftOwn S x)

abbrev background (x : CleanDecoderRate.Sample S) :=
  CleanLeftDecoder.background (exposed S x) upper (CleanDecoderPairLaw.leftOwn S x)

abbrev advice (r : Nat) (A : ManyGoodRows.RowMap (Block rows upper) r)
    (x : CleanDecoderRate.Sample S) :=
  CleanLeftDecoder.advice (exposed S x) upper (h + 1) r A (CleanDecoderPairLaw.leftOwn S x)

abbrev Answer (x : CleanDecoderRate.Sample S) :=
  HierarchicalDecoderTables.Answer (slots S x) upper (h + 1) d

instance answerFintype (x : CleanDecoderRate.Sample S) : Fintype (Answer S x) :=
  HierarchicalDecoderTables.answerFintype (slots S x) upper (h + 1) d

theorem actualInput_eq (r : Nat) (A : ManyGoodRows.RowMap (Block rows upper) r)
    (x : CleanDecoderRate.Sample S) :
    LowerCutDecoderInput.actualInput (slots S x) upper (h + 1)
      (CleanLeftDecoder.arrays (exposed S x) (CleanDecoderPairLaw.leftOwn S x)) A =
        ⟨background S x, advice S r A x⟩ := rfl

variable (hbranch : ∀ k < n, 0 < branch k)

abbrev output (x : CleanDecoderRate.Sample S) (q : CleanDecoderPairLaw.LeftAnswer S x) :
    Answer S x :=
  CleanLeftDecoder.output (exposed S x) upper (h + 1) hbranch d
    (CleanDecoderPairLaw.leftOwn S x) q

abbrev decode (s : Nat) (x : CleanDecoderRate.Sample S)
    (q : CleanDecoderPairLaw.LeftAnswer S x) : Option (Answer S x) :=
  HierarchicalDecoderTables.decode (slots S x) upper (h + 1) hbranch d s q

theorem nativeRank_eq_fullRank (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x) :
    DecoderRankSplit.nativeRank S hbranch x answer =
      HierarchicalDecoderTables.fullRank (slots S x) upper (h + 1) d
        (output S hbranch x answer.1) := rfl

theorem decode_of_highAgrees (s : Nat) (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x)
    (hhigh : DecoderRankSplit.highAgrees S hbranch s x answer = true) :
    decode S hbranch s x answer.1 = some (output S hbranch x answer.1) := by
  have hrank := (DecoderRankSplit.highAgrees_eq_true S hbranch s x answer).mp hhigh
  exact ProjectedNativeCollision.decode_eq_some_of_high
    (slots := slots S x) upper (h + 1) hbranch d s answer.1
    ((nativeRank_eq_fullRank S hbranch x answer) ▸ hrank.1)

theorem highAgrees_eq_highMeeting (s : Nat) (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x) :
    DecoderRankSplit.highAgrees S hbranch s x answer =
      ProjectedFiberSquare.highMeeting (slots S x)
        (CleanDecoderContext.rightSlots (CleanDecoderPairLaw.context S x)
          (CleanDecoderPairLaw.rightOwn S x))
        (CleanDecoderOddLists.fullProjection (CleanDecoderPairLaw.context S x)
          (CleanDecoderPairLaw.occurrences S x)) upper (h + 1) hbranch d s
        answer.1 answer.2 := by
  apply Bool.eq_iff_iff.mpr
  rw [DecoderRankSplit.highAgrees_eq_true]
  simp only [ProjectedFiberSquare.highMeeting, DecoderRankSplit.meeting,
    decide_eq_true_eq, nativeRank_eq_fullRank]
  exact and_congr Iff.rfl eq_comm

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (record : CleanDecoderRate.Record S) →
    CleanLeftDecoder.Useful (CleanDecoderContext.leftExposed (CleanDecoderRate.context S record))
      upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
  (a : OwnInputReference.LowerVector rows (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))
  (threshold : ℝ)

theorem supported_left (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x)
    (hs : (CleanDecoderPairLaw.pairKernel S σ useful r ρ A W a threshold x).weight answer ≠ 0) :
    (CleanLeftDecoder.law (exposed S x) upper (h + 1) σ
      (useful (CleanDecoderRate.observations S x)) r ρ A
      (CleanDecoderPairLaw.leftOwn S x)).weight answer.1 ≠ 0 := by
  intro hz
  apply hs
  change (CleanLeftDecoder.law (exposed S x) upper (h + 1) σ
      (useful (CleanDecoderRate.observations S x)) r ρ A
      (CleanDecoderPairLaw.leftOwn S x)).weight answer.1 *
    (CleanDecoderSeedLaw.rightKernel (CleanDecoderPairLaw.context S x) σ W a threshold
      (CleanDecoderPairLaw.rightOwn S x)).weight answer.2 = 0
  rw [hz, zero_mul]

theorem valid_of_support (hρ : 0 < ρ) (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x)
    (hs : (CleanDecoderPairLaw.pairKernel S σ useful r ρ A W a threshold x).weight answer ≠ 0) :
    HierarchicalLeftDecoder.Valid (slots S x) upper (h + 1) hbranch
      (background S x) answer.1 := by
  exact of_decide_eq_true (DecoderTableAdmissibility.event_of_probability_one
    (CleanLeftDecoder.law (exposed S x) upper (h + 1) σ
      (useful (CleanDecoderRate.observations S x)) r ρ A (CleanDecoderPairLaw.leftOwn S x))
    (fun q => decide (HierarchicalLeftDecoder.Valid (slots S x) upper (h + 1) hbranch
      (background S x) q))
    (CleanLeftDecoder.law_valid (exposed S x) upper (h + 1) σ
      (useful (CleanDecoderRate.observations S x)) hbranch r ρ hρ A
      (CleanDecoderPairLaw.leftOwn S x)) answer.1
    (supported_left S σ useful r ρ A W a threshold x answer hs))

theorem valid_output_of_highAgrees (hρ : 0 < ρ) (s : Nat)
    (x : CleanDecoderRate.Sample S) (answer : CleanDecoderPairLaw.Pair S x)
    (hs : (CleanDecoderPairLaw.pairKernel S σ useful r ρ A W a threshold x).weight answer ≠ 0)
    (hhigh : DecoderRankSplit.highAgrees S hbranch s x answer = true) :
    HierarchicalDecoderTables.Valid (slots S x) upper (h + 1) (background S x)
      hbranch d s (output S hbranch x answer.1) :=
  HierarchicalDecoderTables.decode_valid (slots S x) upper (h + 1) (background S x)
    hbranch d s answer.1
    (valid_of_support S hbranch σ useful r ρ A W a threshold hρ x answer hs)
    (output S hbranch x answer.1) (decode_of_highAgrees S hbranch s x answer hhigh)

theorem responseLaw_eq_pushforward (s : Nat) (x : CleanDecoderRate.Sample S) :
    HierarchicalDecoderTables.responseLaw (slots S x) upper (h + 1) (background S x)
      hbranch σ (useful (CleanDecoderRate.observations S x) (CleanDecoderPairLaw.leftOwn S x))
      r ρ d s (advice S r A x) =
    (CleanDecoderSeedLaw.leftKernel (CleanDecoderPairLaw.context S x) σ
      (useful (CleanDecoderRate.observations S x)) r ρ A
      (CleanDecoderPairLaw.leftOwn S x)).pushforward (decode S hbranch s x) := rfl

theorem pair_decode_law (s : Nat) (x : CleanDecoderRate.Sample S) :
    (CleanDecoderPairLaw.pairKernel S σ useful r ρ A W a threshold x).pushforward
        (fun answer => decode S hbranch s x answer.1) =
      HierarchicalDecoderTables.responseLaw (slots S x) upper (h + 1) (background S x)
        hbranch σ (useful (CleanDecoderRate.observations S x) (CleanDecoderPairLaw.leftOwn S x))
        r ρ d s (advice S r A x) := by
  have hfst :
      (CleanDecoderPairLaw.pairKernel S σ useful r ρ A W a threshold x).pushforward Prod.fst =
        CleanDecoderSeedLaw.leftKernel (CleanDecoderPairLaw.context S x) σ
          (useful (CleanDecoderRate.observations S x)) r ρ A
          (CleanDecoderPairLaw.leftOwn S x) :=
    HiddenBucketBias.product_fst _ _
  rw [← FiniteDistribution.pushforward_comp
    (CleanDecoderPairLaw.pairKernel S σ useful r ρ A W a threshold x)
    (Prod.fst : CleanDecoderPairLaw.Pair S x → CleanDecoderPairLaw.LeftAnswer S x)
    (decode S hbranch s x), hfst]
  exact (responseLaw_eq_pushforward S hbranch σ useful r ρ A s x).symm

end
end PerfectCompleteness.DecoderPairHighOutput

end

section

namespace PerfectCompleteness.FixedDecoderFamilyRate

noncomputable section

open scoped BigOperators Classical
open HierarchicalArrays FixedDecoderCleanRate
open UniqueGamesTheorem.Foundations.Games

theorem expectation_lt_const {O : Type*} [Fintype O]
    (μ : FiniteDistribution O) (f : O → ℝ) (bound : ℝ)
    (hbound : ∀ o, f o < bound) : μ.expectation f < bound := by
  have hpositive : ∃ o, 0 < μ.weight o := by
    by_contra hn
    push Not at hn
    have hzero : ∑ o, μ.weight o = 0 :=
      Finset.sum_eq_zero (fun o _ => le_antisymm (hn o) (μ.nonnegative o))
    linarith [μ.normalized]
  obtain ⟨o, ho⟩ := hpositive
  calc
    μ.expectation f < μ.expectation (fun _ => bound) := by
      apply Finset.sum_lt_sum
      · intro x _
        exact mul_le_mul_of_nonneg_left (hbound x).le (μ.nonnegative x)
      · exact ⟨o, Finset.mem_univ o, mul_lt_mul_of_pos_left (hbound o) ho⟩
    _ = bound := SmallBias.expectation_const μ bound

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
  {O : Type*} [Fintype O] {n h : Nat}
  {upper : O → Nodes (FixedParameters.branch p) n}
  {lower : (o : O) → HierarchicalFrozenTables.LowerNodes (upper o) (h + 1)}
  (G : (o : O) → Geometry p n h (upper o) (lower o))
  (input : List Bool)

def setups (o : O) := setup p (G o) input

variable
  (σ : KeyStrategy.Strategy
    (TreeCanonical.locationCount (FixedParameters.branch p) n
      (FixedRows.sourceLength p.plan hδ)))
  (useful : (o : O) → (record : CleanDecoderRate.Record (setups p G input o)) →
    CleanLeftDecoder.Useful
      (CleanDecoderContext.leftExposed (CleanDecoderRate.context (setups p G input o) record))
      (upper o) (h + 1))
  (r : Nat) (ρ : ℝ)
  (A : (o : O) → ManyGoodRows.RowMap (Block (FixedRows.rows p.plan) (upper o)) r)
  (a : (o : O) → OwnInputReference.LowerVector (FixedRows.rows p.plan)
    (HierarchicalLeftDecoder.LowerNode (upper o) (h + 1) (lower o)))
  (threshold : ℝ) (outer : FiniteDistribution O)

theorem probability_lt_accuracy (unsat : ¬BinaryLanguage.language input)
    (hn : n ≤ p.plan.depth) (hρ : 0 < ρ) :
    (DecoderFamilyLaw.law (setups p G input) σ useful r ρ A a threshold
      outer (p.cubeSize h) (cubePositive p h)).probability
        (DecoderFamilyLaw.lowAgreement (setups p G input) (branchPositive p)
          (FixedRows.cutoff p.plan hδ)) < p.accuracy := by
  rw [DecoderFamilyLaw.probability_eq_expectation]
  apply expectation_lt_const
  intro o
  exact FixedDecoderPairRate.probability_lt_accuracy p (G o) input σ (useful o)
    r ρ (A o) (LinearMap.ker (A o)) (a o) threshold unsat hn hρ

end
end PerfectCompleteness.FixedDecoderFamilyRate

end

section

namespace PerfectCompleteness.FixedDecoderFamilyContradiction

noncomputable section

open scoped Classical
open HierarchicalArrays FixedDecoderCleanRate FixedDecoderFamilyRate
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
  {O : Type*} [Fintype O] {n h : Nat}
  {upper : O → Nodes (FixedParameters.branch p) n}
  {lower : (o : O) → HierarchicalFrozenTables.LowerNodes (upper o) (h + 1)}
  (G : (o : O) → Geometry p n h (upper o) (lower o))
  (input : List Bool)
  (σ : KeyStrategy.Strategy
    (TreeCanonical.locationCount (FixedParameters.branch p) n
      (FixedRows.sourceLength p.plan hδ)))
  (useful : (o : O) → (record : CleanDecoderRate.Record (setups p G input o)) →
    CleanLeftDecoder.Useful
      (CleanDecoderContext.leftExposed (CleanDecoderRate.context (setups p G input o) record))
      (upper o) (h + 1))
  (r : Nat) (ρ : ℝ)
  (A : (o : O) → ManyGoodRows.RowMap (Block (FixedRows.rows p.plan) (upper o)) r)
  (a : (o : O) → OwnInputReference.LowerVector (FixedRows.rows p.plan)
    (HierarchicalLeftDecoder.LowerNode (upper o) (h + 1) (lower o)))
  (threshold : ℝ) (outer : FiniteDistribution O)

theorem impossible (unsat : ¬BinaryLanguage.language input)
    (hn : n ≤ p.plan.depth) (hρ : 0 < ρ)
    (height : Nat) (hheight : height ≤ p.plan.depth)
    (hupper : FixedRankContradiction.gamma p height ≤
      (DecoderFamilyLaw.law (setups p G input) σ useful r ρ A a threshold
        outer (p.cubeSize h) (cubePositive p h)).probability
          (DecoderFamilyLaw.meeting (setups p G input)))
    (hhigh : (DecoderFamilyLaw.law (setups p G input) σ useful r ρ A a threshold
        outer (p.cubeSize h) (cubePositive p h)).probability
          (DecoderFamilyLaw.highAgreement (setups p G input) (branchPositive p)
            (FixedRows.cutoff p.plan hδ)) ^ 2 ≤
      FixedRankContradiction.gamma p height ^ 2 / 8 + 2 * p.accuracy) : False := by
  let μ := DecoderFamilyLaw.law (setups p G input) σ useful r ρ A a threshold
    outer (p.cubeSize h) (cubePositive p h)
  let low := fun z : DecoderFamilyLaw.Sample (setups p G input) =>
    DecoderRankSplit.low (setups p G input z.1) (branchPositive p)
      (FixedRows.cutoff p.plan hδ) z.2.1 z.2.2
  apply FixedRankContradiction.impossible p μ
    (DecoderFamilyLaw.meeting (setups p G input)) low height hheight hupper
  · exact hhigh
  · have hlow := FixedDecoderFamilyRate.probability_lt_accuracy p G input σ useful
      r ρ A a threshold outer unsat hn hρ
    have hevent : (fun z : DecoderFamilyLaw.Sample (setups p G input) =>
        DecoderFamilyLaw.meeting (setups p G input) z && low z) =
        DecoderFamilyLaw.lowAgreement (setups p G input) (branchPositive p)
          (FixedRows.cutoff p.plan hδ) := by
      funext z
      exact DecoderRankSplit.meeting_low (setups p G input z.1) (branchPositive p)
        (FixedRows.cutoff p.plan hδ) z.2.1 z.2.2
    rw [hevent]
    exact hlow

end
end PerfectCompleteness.FixedDecoderFamilyContradiction

end

end OAI
