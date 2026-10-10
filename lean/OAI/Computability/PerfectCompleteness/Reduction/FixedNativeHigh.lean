import OAI.Computability.PerfectCompleteness.Decoding.FixedDecoderCleanRateLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedSourcePhysicalHighLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalHighAverage

namespace OAI

section

namespace PerfectCompleteness.FixedNativeHigh

noncomputable section

open scoped Classical
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height v m : Nat} [NeZero m]
  {upper : Nodes (branch parameters) parameters.plan.depth}
  {d : HierarchicalFrozenTables.LowerNodes upper (height + 1)}
  (S : CleanDecoderRate.Setup (branch parameters) (rows parameters.plan) (repeats parameters.plan)
    parameters.plan.depth height (sourceLength parameters.plan hδ) v m upper d)
  (hnode : WholeArrayInteriorExterior.upperNode (CleanDecoderRate.path S) =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)
  {Original : OriginalDecoderMark.SlotFamily (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ) → Type*}
  [∀ slots, Fintype (Original slots)]
  (F : OriginalDecoderMark.Family (branch parameters) (rows parameters.plan)
    parameters.plan.depth (sourceLength parameters.plan hδ) Original)
  (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ)))
  (r : Nat) (density : ℝ)
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) r)
  (threshold : ℝ)

local instance directionNonempty :
    Nonempty (BucketSampler.Direction (rows parameters.plan (height + 1))) :=
  ⟨BucketUniform.coordinateDirection ⟨0, lt_of_lt_of_le Nat.zero_lt_one
    (parameters.plan.rows_pos (parameters.plan.depth - (height + 1)))⟩⟩

theorem flag_eq (h : Nat) :
    FixedSourceGlobalCollision.flag parameters (height := h) =
      fun _ : Fin (branch parameters h) =>
        ProjectedCleanRate.projectionFlag (parameters.cubeSize h)
          (FixedDecoderCleanRate.cubePositive parameters h) := by
  funext child
  apply FiniteDistribution.eq_of_weight_eq
  intro b
  cases b <;>
    simp [FixedSourceGlobalCollision.flag, ProjectedCleanRate.projectionFlag,
      ProjectionPosterior.bernoulli, RepetitionRate.bernoulli,
      FixedParameters.projectionProbability, ProjectedCleanRate.projectionDensity]

def questionUseful
    (q : FixedSourceGlobalCollision.Questions (m := m) parameters (height := height)) :=
  OriginalDecoderMark.mark F upper (height + 1) κ
    (SourceQuestionLowerForms.slots (CleanDecoderRate.path S) S.outside S.clauses q)

def probability : ℝ :=
  (FiniteDistribution.uniform (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
    (fun direction =>
      (CleanDecoderPairLaw.pairLaw S σ (CleanPhysicalDecoderLaw.useful S F κ)
        r density A (LinearMap.ker A) (CleanPhysicalHighAverage.nativeDirection S hnode direction)
        threshold (parameters.cubeSize height) (FixedDecoderCleanRate.cubePositive parameters height)).probability
          (fun z => DecoderRankSplit.highAgrees S (FixedLowerRawCollision.branchPositive parameters)
            (cutoff parameters.plan hδ) z.1 z.2))

theorem probability_eq_physical :
    probability parameters S hnode F κ σ r density A threshold =
      FixedSourcePhysicalHigh.probability parameters S.outside S.placeholder S.clauses S.designated
        upper (CleanPhysicalHighAverage.suffix S) (CleanPhysicalHighAverage.suffix_proper S)
        d hnode A S.cut S.exterior σ (questionUseful parameters S F κ) density threshold := by
  unfold probability FixedSourcePhysicalHigh.probability
  apply FiniteDistribution.expectation_congr
  intro direction
  rw [CleanPhysicalHighAverage.probability_eq_tag_average S
    (FixedLowerRawCollision.branchPositive parameters) hnode F κ σ r density A direction
    threshold (cutoff parameters.plan hδ) (parameters.cubeSize height)
    (FixedDecoderCleanRate.cubePositive parameters height)]
  simp only [FixedSourcePhysicalHigh.tagLaw, flag_eq]
  apply FiniteDistribution.expectation_congr
  intro q
  apply FiniteDistribution.expectation_congr
  intro tag
  rfl

theorem probability_square_le (hdensity : 0 < density) :
    probability parameters S hnode F κ σ r density A threshold ^ 2 ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 +
        2 * parameters.accuracy := by
  rw [probability_eq_physical]
  exact FixedSourceHighBound.probability_square_le parameters S.outside S.placeholder S.clauses
    S.designated upper (CleanPhysicalHighAverage.suffix S) (CleanPhysicalHighAverage.suffix_proper S)
    d hnode A S.cut S.exterior σ (questionUseful parameters S F κ) density threshold hdensity

end
end PerfectCompleteness.FixedNativeHigh

end

end OAI
