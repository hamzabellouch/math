import OAI.Computability.PerfectCompleteness.Decoding.FixedProjectionErrorLemmas
import OAI.Computability.PerfectCompleteness.Decoding.UpperCutTriangle
import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarCutCalls
import OAI.Computability.PerfectCompleteness.Reduction.FixedStoppedError
import OAI.Computability.PerfectCompleteness.Sampling.CommonProductVariationLemmas
import OAI.Computability.PerfectCompleteness.Sampling.HierarchicalBackgroundVariation

namespace OAI

section

namespace PerfectCompleteness.FixedUpperPairError

open FixedParameters FixedRows DescendantSpaces

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (params : Parameters δ hδ)
  {root upper lower : Nat}

theorem lower_errors_lt (pref : Path (branch params) root (upper + 1))
    (segment : Path (branch params) (upper + 1) (lower + 1))
    (direction : BucketSampler.Direction (rows params.plan (upper + 1)))
    (hroot : root ≤ params.plan.depth) :
    let L : ℝ := ChildBlockCardinality.bound (branch params) lower
      (sourceLength params.plan hδ)
      (UpperScalarCutCalls.count (rows params.plan) (repeats params.plan)
        root (upper + 1) (lower + 1)) (rows params.plan)
    Real.sqrt ((1 + (projectionProbability params lower : ℝ) ^ 2 * (L - 1)) ^
      branch params lower - 1) / 2 +
      Real.sqrt (L ^ 2 / branch params lower) / 2 < 2 * params.accuracy := by
  have hcalls := UpperScalarCutCalls.count_le_fixed_calls params.plan pref segment direction hroot
  have hsparse := FixedProjectionError.sparse_error_lt params hcalls lower
  have hhidden := FixedStoppedError.hidden_error_lt params hcalls lower
  dsimp only
  linarith

theorem three_errors_lt (pref : Path (branch params) root (upper + 1))
    (segment : Path (branch params) (upper + 1) (lower + 1))
    (direction : BucketSampler.Direction (rows params.plan (upper + 1)))
    (hroot : root ≤ params.plan.depth) :
    let L : ℝ := ChildBlockCardinality.bound (branch params) lower
      (sourceLength params.plan hδ)
      (UpperScalarCutCalls.count (rows params.plan) (repeats params.plan)
        root (upper + 1) (lower + 1)) (rows params.plan)
    Real.sqrt ((1 + (projectionProbability params lower : ℝ) ^ 2 * (L - 1)) ^
      branch params lower - 1) / 2 +
      Real.sqrt (L ^ 2 / branch params lower) / 2 +
      Real.sqrt ((ChildBlockCardinality.bound (branch params) upper
        (sourceLength params.plan hδ)
        (OriginalCutCalls.count (rows params.plan) (repeats params.plan) root (upper + 1) + 1)
        (rows params.plan) : ℝ) ^ 2 / branch params upper) / 2 <
      3 * params.accuracy := by
  have hlower := lower_errors_lt params pref segment direction hroot
  have hupper := FixedStoppedError.collision_error_lt params hroot pref.height_le
  dsimp only at hlower ⊢
  linarith

end
end PerfectCompleteness.FixedUpperPairError

end

section

namespace PerfectCompleteness.FixedUpperCutTriangle

open FixedParameters FixedRows RecursiveSpaces DescendantSpaces
open TreeSourceSpaces HierarchicalArrays OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (params : Parameters δ hδ)
  {root upper lower : Nat}

theorem rows_positive (height : Nat) : 0 < rows params.plan height :=
  lt_of_lt_of_le Nat.zero_lt_one (params.plan.rows_pos (params.plan.depth - height))

variable (pref : Path (branch params) root (upper + 1))
  (hcut : lower + 1 ≤ upper + 1)
  (slots : Slots (branch params) root → Fin (sourceLength params.plan hδ) → MixedSupport.Slot)

local instance backgroundFintype :
    Fintype (HierarchicalAgreementMean.Background (rows := rows params.plan) slots (upperNode pref)) :=
  Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots (upperNode pref)) :=
  Fintype.ofFinite _

def upperReferenceLaw :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows params.plan) slots (upperNode pref)) :=
  HierarchicalAgreementMean.referenceLaw slots (upperNode pref)
    (OriginalOwnBucketSplit.backgroundLaw (rows params.plan) (repeats params.plan) pref slots)
    (by simpa only [upperNode_height] using rows_positive params (upper + 1))

variable {Z : UpperCutTriangle.Prefix (branch params) upper lower → Fin (branch params lower) → Type*}
  [∀ lowerPref child, Fintype (Z lowerPref child)]
  (projected : (lowerPref : UpperCutTriangle.Prefix (branch params) upper lower) →
    (child : Fin (branch params lower)) → Z lowerPref child →
      Slots (branch params) lower → Fin (sourceLength params.plan hδ) → MixedSupport.Slot)
  (projection : ∀ lowerPref child z s a, MixedSupport.Projection
    (childSlots (cutSlots (pref.append (GeometricCutSplit.prefixPath hcut lowerPref)) slots) child s a)
    (projected lowerPref child z s a))
  (choiceLaw : (lowerPref : UpperCutTriangle.Prefix (branch params) upper lower) →
    (child : Fin (branch params lower)) → FiniteDistribution (Z lowerPref child))

def modifiedPairLaw :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows params.plan) slots (upperNode pref)) :=
  UpperCutTriangle.modifiedPairLaw (rows params.plan) (repeats params.plan) pref hcut slots
    (fun k _ => branch_pos params k) (rows_positive params (upper + 1))
    projected projection choiceLaw (projectionProbability params lower : ℝ)
    (by exact_mod_cast (projectionProbability_bounds params lower).1.le)
    (by exact_mod_cast (projectionProbability_bounds params lower).2.le)

def originalReferenceLaw :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows params.plan) slots (upperNode pref)) :=
  HierarchicalAgreementMean.referenceLaw slots (upperNode pref)
    ((modifiedPairLaw params pref hcut slots projected projection choiceLaw).pushforward Prod.fst)
    (by simpa only [upperNode_height] using rows_positive params (upper + 1))

theorem modified_reference_lt (hroot : root ≤ params.plan.depth) :
    (modifiedPairLaw params pref hcut slots projected projection choiceLaw).totalVariation
      (upperReferenceLaw params pref slots) < 3 * params.accuracy := by
  have hcomparison := UpperCutTriangle.modified_reference_variation
    (rows params.plan) (repeats params.plan) pref hcut slots
    (fun k _ => branch_pos params k) (rows_positive params (upper + 1))
    projected projection choiceLaw (projectionProbability params lower : ℝ)
    (by exact_mod_cast (projectionProbability_bounds params lower).1.le)
    (by exact_mod_cast (projectionProbability_bounds params lower).2.le)
  let lowerPref : UpperCutTriangle.Prefix (branch params) upper lower :=
    Classical.choice (GeometricCutSplit.prefix_nonempty hcut (fun k _ => branch_pos params k))
  let direction : BucketSampler.Direction (rows params.plan (upper + 1)) :=
    BucketUniform.coordinateDirection ⟨0, rows_positive params (upper + 1)⟩
  have herror := FixedUpperPairError.three_errors_lt params pref
    (GeometricCutSplit.prefixPath hcut lowerPref) direction hroot
  simpa only [modifiedPairLaw, upperReferenceLaw] using hcomparison.trans_lt herror

theorem original_reference_lt (hroot : root ≤ params.plan.depth) :
    (modifiedPairLaw params pref hcut slots projected projection choiceLaw).totalVariation
      (originalReferenceLaw params pref hcut slots projected projection choiceLaw) <
        6 * params.accuracy := by
  have h := HierarchicalBackgroundVariation.original_background_variation slots (upperNode pref)
    (modifiedPairLaw params pref hcut slots projected projection choiceLaw)
    (OriginalOwnBucketSplit.backgroundLaw (rows params.plan) (repeats params.plan) pref slots)
    (by simpa only [upperNode_height] using rows_positive params (upper + 1))
  change (modifiedPairLaw params pref hcut slots projected projection choiceLaw).totalVariation
      (originalReferenceLaw params pref hcut slots projected projection choiceLaw) ≤
    2 * (modifiedPairLaw params pref hcut slots projected projection choiceLaw).totalVariation
      (upperReferenceLaw params pref slots) at h
  have hthree := modified_reference_lt params pref hcut slots projected projection choiceLaw hroot
  linarith

theorem original_reference_le_ten (hroot : root ≤ params.plan.depth) :
    (modifiedPairLaw params pref hcut slots projected projection choiceLaw).totalVariation
      (originalReferenceLaw params pref hcut slots projected projection choiceLaw) ≤
        10 * params.accuracy := by
  have h := original_reference_lt params pref hcut slots projected projection choiceLaw hroot
  have hpositive := params.accuracy_pos
  linarith

end
end PerfectCompleteness.FixedUpperCutTriangle

end

section

namespace PerfectCompleteness.FixedUpperCutFamily

open FixedParameters FixedRows RecursiveSpaces DescendantSpaces
open TreeSourceSpaces HierarchicalArrays OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (params : Parameters δ hδ)
  {root upper lower : Nat} {O : Type*} [Fintype O]
  (pref : O → Path (branch params) root (upper + 1))
  (hcut : lower + 1 ≤ upper + 1)
  (slots : O → Slots (branch params) root → Fin (sourceLength params.plan hδ) → MixedSupport.Slot)

local instance backgroundFintype (o : O) :
    Fintype (HierarchicalAgreementMean.Background (rows := rows params.plan) (slots o) (upperNode (pref o))) :=
  Fintype.ofFinite _

local instance rowSpaceFintype (o : O) :
    Fintype (NodeEmbedding.RowSpace (slots o) (upperNode (pref o))) := Fintype.ofFinite _

abbrev Record := Σ o : O,
  HierarchicalAgreementMean.PairRecord (rows := rows params.plan) (slots o) (upperNode (pref o))

variable {Z : O → UpperCutTriangle.Prefix (branch params) upper lower → Fin (branch params lower) → Type*}
  [∀ o lowerPref child, Fintype (Z o lowerPref child)]
  (projected : (o : O) → (lowerPref : UpperCutTriangle.Prefix (branch params) upper lower) →
    (child : Fin (branch params lower)) → Z o lowerPref child →
      Slots (branch params) lower → Fin (sourceLength params.plan hδ) → MixedSupport.Slot)
  (projection : ∀ o lowerPref child z s a, MixedSupport.Projection
    (childSlots (cutSlots ((pref o).append (GeometricCutSplit.prefixPath hcut lowerPref)) (slots o)) child s a)
    (projected o lowerPref child z s a))
  (choiceLaw : (o : O) → (lowerPref : UpperCutTriangle.Prefix (branch params) upper lower) →
    (child : Fin (branch params lower)) → FiniteDistribution (Z o lowerPref child))

def modifiedLaw (outerLaw : FiniteDistribution O) :
    FiniteDistribution (Record params pref slots) :=
  CompletionSoundness.sigmaLaw outerLaw (fun o =>
    FixedUpperCutTriangle.modifiedPairLaw params (pref o) hcut (slots o)
      (projected o) (projection o) (choiceLaw o))

def referenceLaw (outerLaw : FiniteDistribution O) :
    FiniteDistribution (Record params pref slots) :=
  CompletionSoundness.sigmaLaw outerLaw (fun o =>
    FixedUpperCutTriangle.originalReferenceLaw params (pref o) hcut (slots o)
      (projected o) (projection o) (choiceLaw o))

theorem totalVariation_le_six (outerLaw : FiniteDistribution O)
    (hroot : root ≤ params.plan.depth) :
    (modifiedLaw params pref hcut slots projected projection choiceLaw outerLaw).totalVariation
      (referenceLaw params pref hcut slots projected projection choiceLaw outerLaw) ≤
        6 * params.accuracy := by
  have h := ConditionalVariation.observed_sigma_le_const outerLaw
    (fun o => FixedUpperCutTriangle.modifiedPairLaw params (pref o) hcut (slots o)
      (projected o) (projection o) (choiceLaw o))
    (fun o => FixedUpperCutTriangle.originalReferenceLaw params (pref o) hcut (slots o)
      (projected o) (projection o) (choiceLaw o))
    (6 * params.accuracy)
    (fun o => (FixedUpperCutTriangle.original_reference_lt params (pref o) hcut (slots o)
      (projected o) (projection o) (choiceLaw o) hroot).le)
    (id : Record params pref slots → Record params pref slots)
  simpa only [modifiedLaw, referenceLaw, FiniteDistribution.pushforward_id] using h

theorem observed_totalVariation_le_ten {Γ : Type*} [Fintype Γ]
    (outerLaw : FiniteDistribution O) (hroot : root ≤ params.plan.depth)
    (observe : Record params pref slots → Γ) :
    ((modifiedLaw params pref hcut slots projected projection choiceLaw outerLaw).pushforward observe).totalVariation
      ((referenceLaw params pref hcut slots projected projection choiceLaw outerLaw).pushforward observe) ≤
        10 * params.accuracy := by
  have h := (DensityVariation.variation_pushforward_le _ _ observe).trans
    (totalVariation_le_six params pref hcut slots projected projection choiceLaw outerLaw hroot)
  have hpositive := params.accuracy_pos
  linarith

end
end PerfectCompleteness.FixedUpperCutFamily

end

end OAI
