import OAI.Computability.PerfectCompleteness.Decoding.FixedStoppedDecoderContext
import OAI.Computability.PerfectCompleteness.Sampling.CandidateCoupling

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedDirections

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j)

abbrev lowerNode (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :=
  HierarchicalLeftDecoder.LowerNode (FixedStoppedDecoderContext.upper parameters i j pref)
    (i.val + 1) (FixedStoppedDecoderContext.lower parameters i j hij pref)

@[simp] theorem lowerNode_height (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :
    Nodes.height (lowerNode parameters i j hij pref) = i.val + 1 :=
  CleanDecoderContext.lowerHeight (FixedStoppedDecoderContext.upper parameters i j pref)
    (FixedStoppedDecoderContext.lower parameters i j hij pref)

abbrev LowerDirection (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :=
  BucketSampler.Direction
    (FixedRows.rows parameters.plan (Nodes.height (lowerNode parameters i j hij pref)))

instance lowerDirectionNonempty (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :
    Nonempty (LowerDirection parameters i j hij pref) :=
  PreliminarySampler.directionNonempty _ (by
    rw [lowerNode_height]
    exact parameters.plan.rows_pos (parameters.plan.depth - (i.val + 1)))

def lowerDirectionEquiv (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :
    PrefixTests.LevelDirection (FixedRows.rows parameters.plan) i ≃
      LowerDirection parameters i j hij pref :=
  (Equiv.cast (congrArg (fun height =>
    BucketSampler.Direction (FixedRows.rows parameters.plan height))
      (lowerNode_height parameters i j hij pref))).symm

def lowerDirection (pref : FixedStoppedDecoderContext.Prefixes parameters i j)
    (directions : FixedStoppedDecoderContext.Directions parameters) :
    LowerDirection parameters i j hij pref :=
  PrefixTests.nodeDirection (FixedRows.rows parameters.plan) i
    ⟨lowerNode parameters i j hij pref, lowerNode_height parameters i j hij pref⟩ (directions i)

theorem lowerDirection_eq_equiv (pref : FixedStoppedDecoderContext.Prefixes parameters i j)
    (directions : FixedStoppedDecoderContext.Directions parameters) :
    lowerDirection parameters i j hij pref directions =
      lowerDirectionEquiv parameters i j hij pref (directions i) := rfl

def lowerLaw (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :
    FiniteDistribution (LowerDirection parameters i j hij pref) :=
  FiniteDistribution.uniform _

theorem coordinate_law (level : Fin parameters.plan.depth) :
    (FixedStoppedDecoderContext.directionLaw parameters).pushforward
        (fun directions => directions level) =
      CanonicalDirections.levelLaw (FixedRows.rows parameters.plan)
        (fun k => parameters.plan.rows_pos (parameters.plan.depth - (k + 1))) level :=
  FiniteProduct.eval_pushforward
    (CanonicalDirections.levelLaw (FixedRows.rows parameters.plan)
      (fun k => parameters.plan.rows_pos (parameters.plan.depth - (k + 1)))) level

theorem lowerDirection_law (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :
    (FixedStoppedDecoderContext.directionLaw parameters).pushforward
        (lowerDirection parameters i j hij pref) = lowerLaw parameters i j hij pref := by
  let : Nonempty (PrefixTests.LevelDirection (FixedRows.rows parameters.plan) i) :=
    PreliminarySampler.directionNonempty _
      (parameters.plan.rows_pos (parameters.plan.depth - (i.val + 1)))
  change (FixedStoppedDecoderContext.directionLaw parameters).pushforward
    (fun directions => lowerDirectionEquiv parameters i j hij pref (directions i)) = _
  rw [← FiniteDistribution.pushforward_comp (FixedStoppedDecoderContext.directionLaw parameters)
    (fun directions => directions i) (lowerDirectionEquiv parameters i j hij pref), coordinate_law]
  change (FiniteDistribution.uniform (PrefixTests.LevelDirection (FixedRows.rows parameters.plan) i)).pushforward
    (lowerDirectionEquiv parameters i j hij pref) =
      FiniteDistribution.uniform (LowerDirection parameters i j hij pref)
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport (lowerDirectionEquiv parameters i j hij pref)

theorem lowerDirection_expectation (pref : FixedStoppedDecoderContext.Prefixes parameters i j)
    (f : LowerDirection parameters i j hij pref → ℝ) :
    (FixedStoppedDecoderContext.directionLaw parameters).expectation
        (fun directions => f (lowerDirection parameters i j hij pref directions)) =
      (lowerLaw parameters i j hij pref).expectation f := by
  rw [← lowerDirection_law, FiniteDistribution.expectation_pushforward]

variable (input : List Bool)

theorem direction_eq (context : FixedStoppedDecoderContext.Context parameters i j hij input) :
    FixedStoppedDecoderContext.direction parameters i j hij input context =
      (lowerDirection parameters i j hij context.1 context.2.2.2.1).val := rfl

theorem expectation_coordinate
    (f : (pref : FixedStoppedDecoderContext.Prefixes parameters i j) →
      (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref) →
      FixedStoppedDecoderContext.Advice parameters i j pref →
      FixedStoppedDecoderContext.Exterior parameters i j hij input pref external →
      PrefixTests.LevelDirection (FixedRows.rows parameters.plan) i → ℝ) :
    (FixedStoppedDecoderContext.law parameters i j hij input).expectation (fun context =>
      f context.1 context.2.1 context.2.2.1 context.2.2.2.2 (context.2.2.2.1 i)) =
    (FixedStoppedDecoderContext.prefixLaw parameters i j hij).expectation (fun pref =>
      (FiniteDistribution.uniform
        (FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)).expectation
          (fun external =>
        (FiniteDistribution.uniform (FixedStoppedDecoderContext.Advice parameters i j pref)).expectation
          (fun A =>
          (FiniteDistribution.uniform
            (FixedStoppedDecoderContext.Exterior parameters i j hij input pref external)).expectation
              (fun exterior =>
            (CanonicalDirections.levelLaw (FixedRows.rows parameters.plan)
              (fun k => parameters.plan.rows_pos (parameters.plan.depth - (k + 1))) i).expectation
                (fun direction => f pref external A exterior direction))))) := by
  rw [FixedStoppedDecoderContext.law, CandidateCoupling.expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro pref
  rw [CandidateCoupling.expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro external
  rw [FixedStoppedDecoderContext.fiberLaw, FiniteDistribution.expectation_product]
  apply FiniteDistribution.expectation_congr
  intro A
  rw [FiniteDistribution.expectation_product, FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro exterior
  rw [← coordinate_law parameters i, FiniteDistribution.expectation_pushforward]

theorem expectation_lowerDirection
    (f : (pref : FixedStoppedDecoderContext.Prefixes parameters i j) →
      (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref) →
      FixedStoppedDecoderContext.Advice parameters i j pref →
      FixedStoppedDecoderContext.Exterior parameters i j hij input pref external →
      LowerDirection parameters i j hij pref → ℝ) :
    (FixedStoppedDecoderContext.law parameters i j hij input).expectation (fun context =>
      f context.1 context.2.1 context.2.2.1 context.2.2.2.2
        (lowerDirection parameters i j hij context.1 context.2.2.2.1)) =
    (FixedStoppedDecoderContext.prefixLaw parameters i j hij).expectation (fun pref =>
      (FiniteDistribution.uniform
        (FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)).expectation
          (fun external =>
        (FiniteDistribution.uniform (FixedStoppedDecoderContext.Advice parameters i j pref)).expectation
          (fun A =>
          (FiniteDistribution.uniform
            (FixedStoppedDecoderContext.Exterior parameters i j hij input pref external)).expectation
              (fun exterior =>
            (lowerLaw parameters i j hij pref).expectation
              (fun direction => f pref external A exterior direction))))) := by
  rw [FixedStoppedDecoderContext.law, CandidateCoupling.expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro pref
  rw [CandidateCoupling.expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro external
  rw [FixedStoppedDecoderContext.fiberLaw, FiniteDistribution.expectation_product]
  apply FiniteDistribution.expectation_congr
  intro A
  rw [FiniteDistribution.expectation_product, FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro exterior
  exact lowerDirection_expectation parameters i j hij pref (f pref external A exterior)

theorem expectation_direction
    (f : (pref : FixedStoppedDecoderContext.Prefixes parameters i j) →
      (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref) →
      FixedStoppedDecoderContext.Advice parameters i j pref →
      FixedStoppedDecoderContext.Exterior parameters i j hij input pref external →
      Block (FixedRows.rows parameters.plan) (lowerNode parameters i j hij pref) → ℝ) :
    (FixedStoppedDecoderContext.law parameters i j hij input).expectation (fun context =>
      f context.1 context.2.1 context.2.2.1 context.2.2.2.2
        (FixedStoppedDecoderContext.direction parameters i j hij input context)) =
    (FixedStoppedDecoderContext.prefixLaw parameters i j hij).expectation (fun pref =>
      (FiniteDistribution.uniform
        (FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)).expectation
          (fun external =>
        (FiniteDistribution.uniform (FixedStoppedDecoderContext.Advice parameters i j pref)).expectation
          (fun A =>
          (FiniteDistribution.uniform
            (FixedStoppedDecoderContext.Exterior parameters i j hij input pref external)).expectation
              (fun exterior =>
            (lowerLaw parameters i j hij pref).expectation
              (fun direction => f pref external A exterior direction.val))))) :=
  expectation_lowerDirection parameters i j hij input
    (fun pref external A exterior direction => f pref external A exterior direction.val)

end
end PerfectCompleteness.FixedStoppedDirections

end

end OAI
