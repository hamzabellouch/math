import OAI.Computability.PerfectCompleteness.Decoding.FixedStoppedDecoderLaw
import OAI.Computability.PerfectCompleteness.Machines.LowerCutInstalledInput
import OAI.Computability.PerfectCompleteness.Reduction.FixedNativeHigh
import OAI.Computability.PerfectCompleteness.Reduction.FixedStoppedDirections

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedHighBound

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

abbrev Prefixes := FixedStoppedDecoderContext.Prefixes parameters i j

def setup (pref : Prefixes parameters i j)
    (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
    (exterior : FixedStoppedDecoderContext.Exterior parameters i j hij input pref external) :=
  FixedDecoderCleanRate.setup parameters
    (StoppedCleanGeometry.geometry parameters input
      (FixedStoppedDecoderContext.upperPath parameters i j pref)
      (FixedStoppedDecoderContext.lowerPath parameters i j hij pref) hij external exterior) input

theorem setup_node (pref : Prefixes parameters i j)
    (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
    (exterior : FixedStoppedDecoderContext.Exterior parameters i j hij input pref external) :
    WholeArrayInteriorExterior.upperNode
        (CleanDecoderRate.path (setup parameters i j hij input pref external exterior)) =
      FixedStoppedDirections.lowerNode parameters i j hij pref := by
  change WholeArrayInteriorExterior.upperNode
      (CleanRecordDecoderInput.path _ _
        (StoppedCleanGeometry.geometry parameters input
          (FixedStoppedDecoderContext.upperPath parameters i j pref)
          (FixedStoppedDecoderContext.lowerPath parameters i j hij pref) hij external exterior).cut) = _
  rw [StoppedCleanGeometry.geometry_path]
  exact (StoppedCleanGeometry.lowerNode_descendant
    (FixedStoppedDecoderContext.upperPath parameters i j pref)
    (FixedStoppedDecoderContext.lowerPath parameters i j hij pref) hij).symm

def highProbability (strategy : FixedPreliminaryGame.Strategy parameters input)
    (pref : Prefixes parameters i j)
    (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
    (A : FixedStoppedDecoderContext.Advice parameters i j pref)
    (exterior : FixedStoppedDecoderContext.Exterior parameters i j hij input pref external)
    (a : Block (FixedRows.rows parameters.plan)
      (FixedStoppedDirections.lowerNode parameters i j hij pref)) : ℝ :=
  (CleanDecoderPairLaw.pairLaw (setup parameters i j hij input pref external exterior)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (CleanPhysicalDecoderLaw.useful (setup parameters i j hij input pref external exterior)
      (FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy pref)
      (InitialParameters.useful δ)) parameters.plan.order parameters.plan.density A
    (LinearMap.ker A) a (FixedStoppedDecoderLaw.threshold parameters j)
    (parameters.cubeSize i.val) (FixedDecoderCleanRate.cubePositive parameters i.val)).probability
      (fun z => DecoderRankSplit.highAgrees
        (setup parameters i j hij input pref external exterior)
        (FixedDecoderCleanRate.branchPositive parameters)
        (FixedRows.cutoff parameters.plan hδ) z.1 z.2)

def directionMean (strategy : FixedPreliminaryGame.Strategy parameters input)
    (pref : Prefixes parameters i j)
    (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
    (A : FixedStoppedDecoderContext.Advice parameters i j pref)
    (exterior : FixedStoppedDecoderContext.Exterior parameters i j hij input pref external) : ℝ :=
  (FixedStoppedDirections.lowerLaw parameters i j hij pref).expectation
    (fun a => highProbability parameters i j hij input strategy pref external A exterior a.val)

private theorem castDirection_eq {branch rows : Nat → Nat} {n : Nat}
    {node node' : Nodes branch n} (h : node = node')
    (a : BucketSampler.Direction (rows (Nodes.height node))) :
    ProjectedFiberRawPair.castDirection h a =
      LowerCutInstalledInput.directionCast rows h a := by
  cases h
  rfl

theorem directionMean_eq_native
    (strategy : FixedPreliminaryGame.Strategy parameters input)
    (pref : Prefixes parameters i j)
    (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
    (A : FixedStoppedDecoderContext.Advice parameters i j pref)
    (exterior : FixedStoppedDecoderContext.Exterior parameters i j hij input pref external) :
    directionMean parameters i j hij input strategy pref external A exterior =
      FixedNativeHigh.probability parameters (setup parameters i j hij input pref external exterior)
        (setup_node parameters i j hij input pref external exterior)
        (FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy pref)
        (InitialParameters.useful δ) (FixedStoppedDecoderLaw.labeling parameters input strategy)
        parameters.plan.order parameters.plan.density A
        (FixedStoppedDecoderLaw.threshold parameters j) := by
  let : Nonempty (BucketSampler.Direction (FixedRows.rows parameters.plan (i.val + 1))) :=
    PreliminarySampler.directionNonempty _
      (parameters.plan.rows_pos (parameters.plan.depth - (i.val + 1)))
  let e := LowerCutInstalledInput.lowerDirectionEquiv (FixedRows.rows parameters.plan)
    (CleanDecoderRate.path (setup parameters i j hij input pref external exterior))
    (FixedStoppedDecoderContext.upper parameters i j pref) (i.val + 1)
    (FixedStoppedDecoderContext.lower parameters i j hij pref)
    (setup_node parameters i j hij input pref external exterior)
  have htransport :
      (FiniteDistribution.uniform
        (BucketSampler.Direction (FixedRows.rows parameters.plan (i.val + 1)))).pushforward e =
      FixedStoppedDirections.lowerLaw parameters i j hij pref := by
    rw [← FiniteDistribution.transport_eq_pushforward]
    exact UniformConditioning.uniform_transport e
  unfold directionMean
  rw [← htransport, FiniteDistribution.expectation_pushforward]
  unfold FixedNativeHigh.probability
  apply FiniteDistribution.expectation_congr
  intro a
  have hdirection : e a =
      ProjectedFiberRawPair.direction
        (CleanDecoderRate.path (setup parameters i j hij input pref external exterior))
        (FixedStoppedDecoderContext.upper parameters i j pref) (i.val + 1)
        (FixedStoppedDecoderContext.lower parameters i j hij pref)
        (setup_node parameters i j hij input pref external exterior) a := by
    unfold e LowerCutInstalledInput.lowerDirectionEquiv ProjectedFiberRawPair.direction
    exact (castDirection_eq _ _).symm
  rw [hdirection]
  rfl

theorem directionMean_square_le
    (strategy : FixedPreliminaryGame.Strategy parameters input)
    (pref : Prefixes parameters i j)
    (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
    (A : FixedStoppedDecoderContext.Advice parameters i j pref)
    (exterior : FixedStoppedDecoderContext.Exterior parameters i j hij input pref external) :
    directionMean parameters i j hij input strategy pref external A exterior ^ 2 ≤
      FixedRankContradiction.gamma parameters (j.val + 1) ^ 2 / 8 + 2 * parameters.accuracy := by
  rw [directionMean_eq_native]
  simpa only [WholeArrayInteriorExterior.upperNode_height] using
    FixedNativeHigh.probability_square_le parameters
      (setup parameters i j hij input pref external exterior)
      (setup_node parameters i j hij input pref external exterior)
      (FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy pref)
      (InitialParameters.useful δ) (FixedStoppedDecoderLaw.labeling parameters input strategy)
      parameters.plan.order parameters.plan.density A
      (FixedStoppedDecoderLaw.threshold parameters j) parameters.plan.density_pos

theorem probability_eq_mean (strategy : FixedPreliminaryGame.Strategy parameters input) :
    (FixedStoppedDecoderLaw.law parameters i j hij input strategy).probability
        (FixedStoppedDecoderLaw.highAgreement parameters i j hij input) =
      (FixedStoppedDecoderContext.prefixLaw parameters i j hij).expectation (fun pref =>
        (FiniteDistribution.uniform
          (FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)).expectation
            (fun external =>
          (FiniteDistribution.uniform
            (FixedStoppedDecoderContext.Advice parameters i j pref)).expectation (fun A =>
            (FiniteDistribution.uniform
              (FixedStoppedDecoderContext.Exterior parameters i j hij input pref external)).expectation
                (directionMean parameters i j hij input strategy pref external A)))) := by
  exact (DecoderFamilyLaw.probability_eq_expectation
    (FixedStoppedDecoderLaw.setups parameters i j hij input)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (FixedStoppedDecoderLaw.useful parameters i j hij input strategy)
    parameters.plan.order parameters.plan.density
    (FixedStoppedDecoderContext.advice parameters i j hij input)
    (FixedStoppedDecoderContext.direction parameters i j hij input)
    (FixedStoppedDecoderLaw.threshold parameters j)
    (FixedStoppedDecoderContext.law parameters i j hij input)
    (parameters.cubeSize i.val) (FixedDecoderCleanRate.cubePositive parameters i.val)
    (FixedStoppedDecoderLaw.highAgreement parameters i j hij input)).trans
      (FixedStoppedDirections.expectation_direction parameters i j hij input
        (highProbability parameters i j hij input strategy))

private theorem mean_square_le_const {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (f : Ω → ℝ) (bound : ℝ)
    (hbound : ∀ x, f x ^ 2 ≤ bound) : μ.expectation f ^ 2 ≤ bound := by
  calc
    _ ≤ μ.expectation (fun x => f x ^ 2) := CollisionAveraging.mean_square_le μ f
    _ ≤ μ.expectation (fun _ => bound) := SmallBias.expectation_mono μ hbound
    _ = bound := SmallBias.expectation_const μ bound

theorem probability_square_le (strategy : FixedPreliminaryGame.Strategy parameters input) :
    (FixedStoppedDecoderLaw.law parameters i j hij input strategy).probability
        (FixedStoppedDecoderLaw.highAgreement parameters i j hij input) ^ 2 ≤
      FixedRankContradiction.gamma parameters (j.val + 1) ^ 2 / 8 + 2 * parameters.accuracy := by
  rw [probability_eq_mean]
  apply mean_square_le_const
  intro pref
  apply mean_square_le_const
  intro external
  apply mean_square_le_const
  intro A
  apply mean_square_le_const
  intro exterior
  exact directionMean_square_le parameters i j hij input strategy pref external A exterior

end
end PerfectCompleteness.FixedStoppedHighBound

end

end OAI
