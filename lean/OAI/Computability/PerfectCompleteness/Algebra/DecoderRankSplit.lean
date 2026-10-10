import OAI.Computability.PerfectCompleteness.Algebra.FixedRankContradiction
import OAI.Computability.PerfectCompleteness.Decoding.FixedDecoderCleanRateLemmas

namespace OAI

section

namespace PerfectCompleteness.DecoderRankSplit

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

def meeting (x : CleanDecoderRate.Sample S) (answer : CleanDecoderPairLaw.Pair S x) : Bool :=
  decide (answer.2 = DecoderSourcePullback.upperTarget
    (CleanDecoderOddLists.fullProjection (CleanDecoderPairLaw.context S x)
      (CleanDecoderPairLaw.occurrences S x)) upper answer.1)

variable (hbranch : ∀ k < n, 0 < branch k)

def nativeRank (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x) : Nat :=
  OddListExtraction.formRank
    (H (CleanDecoderOddLists.leftNative (CleanDecoderPairLaw.context S x)
      (CleanDecoderPairLaw.leftOwn S x)))
    (CleanLeftDecoder.form
      (CleanDecoderContext.leftExposed (CleanDecoderPairLaw.context S x)) upper (h + 1)
      hbranch d (CleanDecoderPairLaw.leftOwn S x) answer.1)

def low (s : Nat) (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x) : Bool :=
  decide (nativeRank S hbranch x answer ≤ s)

def highAgrees (s : Nat) (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x) : Bool :=
  meeting S x answer && !(low S hbranch s x answer)

@[simp] theorem highAgrees_eq_true (s : Nat) (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x) :
    highAgrees S hbranch s x answer = true ↔
      s < nativeRank S hbranch x answer ∧ meeting S x answer = true := by
  simp [highAgrees, low, and_comm]

private theorem decide_and_comm (P Q : Prop) [Decidable P] [Decidable Q] :
    (decide P && decide Q) = decide (Q ∧ P) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem meeting_low (s : Nat) (x : CleanDecoderRate.Sample S)
    (answer : CleanDecoderPairLaw.Pair S x) :
    (meeting S x answer && low S hbranch s x answer) =
      CleanDecoderPairLaw.pairAgrees S hbranch s x answer :=
  decide_and_comm
    (answer.2 = DecoderSourcePullback.upperTarget
      (CleanDecoderOddLists.fullProjection (CleanDecoderPairLaw.context S x)
        (CleanDecoderPairLaw.occurrences S x)) upper answer.1)
    (nativeRank S hbranch x answer ≤ s)

theorem probability_split
    (μ : FiniteDistribution (Σ x : CleanDecoderRate.Sample S, CleanDecoderPairLaw.Pair S x))
    (s : Nat) :
    μ.probability (fun z => meeting S z.1 z.2) =
      μ.probability (fun z => CleanDecoderPairLaw.pairAgrees S hbranch s z.1 z.2) +
      μ.probability (fun z => highAgrees S hbranch s z.1 z.2) := by
  have hsplit := FixedRankContradiction.probability_split μ
    (fun z => meeting S z.1 z.2) (fun z => low S hbranch s z.1 z.2)
  simpa only [meeting_low, highAgrees] using hsplit

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (record : CleanDecoderRate.Record S) →
    CleanLeftDecoder.Useful (CleanDecoderContext.leftExposed (CleanDecoderRate.context S record))
      upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
  (a : OwnInputReference.LowerVector rows (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))
  (threshold : ℝ)

theorem pair_probability_split (s cube : Nat) (hcube : 0 < cube) :
    (CleanDecoderPairLaw.pairLaw S σ useful r ρ A W a threshold cube hcube).probability
      (fun z => meeting S z.1 z.2) =
    (CleanDecoderPairLaw.pairLaw S σ useful r ρ A W a threshold cube hcube).probability
      (fun z => CleanDecoderPairLaw.pairAgrees S hbranch s z.1 z.2) +
    (CleanDecoderPairLaw.pairLaw S σ useful r ρ A W a threshold cube hcube).probability
      (fun z => highAgrees S hbranch s z.1 z.2) :=
  probability_split S hbranch _ s

end
end PerfectCompleteness.DecoderRankSplit

end

end OAI
