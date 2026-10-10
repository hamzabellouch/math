import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarPairAveraging
import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CommonProductVariationLemmas

namespace OAI

section

namespace PerfectCompleteness.UpperCutTriangle

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

private theorem sigma_snd {S A : Type*} [Fintype S] [Fintype A]
    (μ : FiniteDistribution S) (P : S → FiniteDistribution A) :
    (CompletionSoundness.sigmaLaw μ P).pushforward (fun x => x.2) = μ.mixture P := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, CompletionSoundness.sigmaLaw_probability,
    FiniteDistribution.probability_mixture]
  rfl

private theorem mixture_variation_le {S A : Type*} [Fintype S] [Fintype A]
    (μ : FiniteDistribution S) (P Q : S → FiniteDistribution A) (error : ℝ)
    (h : ∀ s, (P s).totalVariation (Q s) ≤ error) :
    (μ.mixture P).totalVariation (μ.mixture Q) ≤ error := by
  have hmix := ConditionalVariation.observed_sigma_le_const μ P Q error h
    (fun x : Σ _ : S, A => x.2)
  simpa only [sigma_snd] using hmix

private theorem variation_triangle {A : Type*} [Fintype A]
    (P U Q : FiniteDistribution A) :
    P.totalVariation Q ≤ P.totalVariation U + U.totalVariation Q := by
  unfold FiniteDistribution.totalVariation
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => abs_sub_le (P.weight x) (U.weight x) (Q.weight x))
  rw [Finset.sum_add_distrib] at h
  linarith

variable {branch : Nat → Nat} {n j i t : Nat}

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalAgreementMean.Background (rows := rows) slots (upperNode p)) := Fintype.ofFinite _

local instance rowSpaceFintype (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _

abbrev Prefix (branch : Nat → Nat) (j i : Nat) := GeometricCutSplit.Prefix branch (j + 1) (i + 1)

variable {Z : Prefix branch j i → Fin (branch i) → Type*}
  [∀ pref c, Fintype (Z pref c)]

def modifiedPairLaw (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (hcut : i + 1 ≤ j + 1) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : 0 < rows (j + 1))
    (projected : (pref : Prefix branch j i) → (c : Fin (branch i)) → Z pref c →
      Slots branch i → Fin t → MixedSupport.Slot)
    (projection : ∀ pref c z s a, MixedSupport.Projection
      (childSlots (cutSlots (p.append (GeometricCutSplit.prefixPath hcut pref)) slots) c s a)
      (projected pref c z s a))
    (choiceLaw : (pref : Prefix branch j i) → (c : Fin (branch i)) → FiniteDistribution (Z pref c))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p)) :=
  (GeometricCutSplit.prefixLaw hcut hbranch).mixture (fun pref =>
    UpperScalarPairComparison.pairLaw rows repeats p (GeometricCutSplit.prefixPath hcut pref)
      slots (OriginalCutPairLaw.directionsLaw rows j hrows)
      (ProjectedPrefixComparison.assembledLaw
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows
        (cutSlots (p.append (GeometricCutSplit.prefixPath hcut pref)) slots)
        (projected pref) (projection pref) (choiceLaw pref) β hβ hβ'))

theorem modified_reference_variation (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (hcut : i + 1 ≤ j + 1) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : 0 < rows (j + 1))
    (projected : (pref : Prefix branch j i) → (c : Fin (branch i)) → Z pref c →
      Slots branch i → Fin t → MixedSupport.Slot)
    (projection : ∀ pref c z s a, MixedSupport.Projection
      (childSlots (cutSlots (p.append (GeometricCutSplit.prefixPath hcut pref)) slots) c s a)
      (projected pref c z s a))
    (choiceLaw : (pref : Prefix branch j i) → (c : Fin (branch i)) → FiniteDistribution (Z pref c))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (modifiedPairLaw rows repeats p hcut slots hbranch hrows projected projection choiceLaw β hβ hβ').totalVariation
      (HierarchicalAgreementMean.referenceLaw slots (upperNode p)
        (OriginalOwnBucketSplit.backgroundLaw rows repeats p slots)
        (by simpa only [upperNode_height] using hrows)) ≤
      Real.sqrt ((1 + β ^ 2 * ((ChildBlockCardinality.bound branch i t
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows : ℝ) - 1)) ^ branch i - 1) / 2 +
      Real.sqrt ((ChildBlockCardinality.bound branch i t
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows : ℝ) ^ 2 / branch i) / 2 +
      Real.sqrt ((ChildBlockCardinality.bound branch j t
        (OriginalCutCalls.count rows repeats n (j + 1) + 1) rows : ℝ) ^ 2 / branch j) / 2 := by
  let directions := OriginalCutPairLaw.directionsLaw rows j hrows
  let ν := GeometricPath.law i (fun k hk =>
    hbranch k (Nat.lt_of_lt_of_le (Nat.lt_trans hk (Nat.lt_succ_self i)) hcut))
  let lowerOriginal := fun pref : Prefix branch j i =>
    UpperScalarPairComparison.pairLaw rows repeats p (GeometricCutSplit.prefixPath hcut pref)
      slots directions
      (OriginalPrefixContinuation.assembledLaw
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows repeats
        (cutSlots (p.append (GeometricCutSplit.prefixPath hcut pref)) slots) ν GeometricPath.leafPath
        (hbranch i (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hcut)))
  have hlower := mixture_variation_le (GeometricCutSplit.prefixLaw hcut hbranch)
    (fun pref => UpperScalarPairComparison.pairLaw rows repeats p
      (GeometricCutSplit.prefixPath hcut pref) slots directions
      (ProjectedPrefixComparison.assembledLaw
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows
        (cutSlots (p.append (GeometricCutSplit.prefixPath hcut pref)) slots)
        (projected pref) (projection pref) (choiceLaw pref) β hβ hβ'))
    lowerOriginal _ (fun pref =>
      UpperScalarPairComparison.modified_original_variation rows repeats p
        (GeometricCutSplit.prefixPath hcut pref) slots
        (projected pref) (projection pref) (choiceLaw pref) β hβ hβ'
        ν GeometricPath.leafPath
        (hbranch i (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hcut)) directions)
  have heq := UpperScalarPairAveraging.geometric_average_eq_actual rows repeats p hcut slots
    directions hbranch
  change (GeometricCutSplit.prefixLaw hcut hbranch).mixture lowerOriginal = _ at heq
  rw [heq] at hlower
  have hupper := OriginalCutPairLaw.actual_pair_totalVariation_le rows repeats p slots
    (GeometricPath.law j (fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self j))))
    GeometricPath.leafPath (hbranch j (Nat.lt_succ_self j)) hrows
  exact (variation_triangle _ _ _).trans (add_le_add hlower hupper)

end
end PerfectCompleteness.UpperCutTriangle

end

end OAI
