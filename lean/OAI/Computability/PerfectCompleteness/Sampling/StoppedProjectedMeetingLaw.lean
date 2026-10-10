import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalProjectedPredictionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedPhysicalAdvice

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedMeetingLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
attribute [local instance] linearMapFintype
attribute [local instance] StoppedProjectedPhysicalAdvice.adviceFintype
  StoppedProjectedPhysicalAdvice.physicalAdviceFintype
  StoppedProjectedPhysicalAdvice.rawFiberFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ)

theorem rows_positive (k : Nat) : 0 < FixedRows.rows plan (k + 1) :=
  plan.rows_pos (plan.depth - (k + 1))

variable {branch : Nat → Nat} {i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (hupper : j + 1 ≤ plan.depth) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

abbrev Sample := StoppedProjectedPhysicalAdvice.Sample (t := t) clauses
  (FixedRows.rows plan) (FixedRows.repeats plan) hupper hij designated plan.order

abbrev RawSample := StoppedProjectedPhysicalAdvice.RawSample (t := t) clauses
  (FixedRows.rows plan) (FixedRows.repeats plan) hupper hij designated plan.order

variable [NeZero m]
  (hbranch : ∀ k < plan.depth, 0 < branch k)
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))

def rawMeetingProbability
    (sample : RawSample (t := t) plan clauses hupper hij designated) : ℝ :=
  HierarchicalProjectedAverage.meetingProbability plan
    (StoppedProjectedExperiment.nativeSlots clauses sample.1)
    (StoppedProjectedExperiment.projectedSlots clauses (FixedRows.rows plan)
      hupper hij designated sample.1)
    (StoppedProjectedExperiment.projection clauses (FixedRows.rows plan)
      hupper hij designated sample.1)
    (StoppedProjectedExperiment.upper hupper sample.1) (i + 1)
    (StoppedProjectedExperiment.lower (FixedRows.rows plan) hupper hij sample.1)
    (StoppedProjectedExperiment.cut (FixedRows.rows plan) hupper hij sample.1)
    (StoppedProjectedExperiment.direction (FixedRows.rows plan) hupper hij sample.1)
    (StoppedProjectedExperiment.innerLaw (FixedRows.rows plan) hij
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper))
      (rows_positive plan) flag) σ sample.2

def meetingProbability
    (sample : Sample (t := t) plan clauses hupper hij designated) : ℝ :=
  rawMeetingProbability plan clauses hupper hij designated hbranch flag σ
    (StoppedProjectedPhysicalAdvice.read clauses (FixedRows.rows plan)
      (FixedRows.repeats plan) hupper hij designated plan.order sample)

abbrev expectedMeeting : ℝ :=
  HierarchicalProjectedOuterAverage.expectedMeeting plan
    (StoppedProjectedExperiment.nativeSlots clauses)
    (StoppedProjectedExperiment.projectedSlots clauses (FixedRows.rows plan)
      hupper hij designated)
    (StoppedProjectedExperiment.projection clauses (FixedRows.rows plan)
      hupper hij designated)
    (StoppedProjectedExperiment.upper hupper) (i + 1)
    (StoppedProjectedExperiment.lower (FixedRows.rows plan) hupper hij)
    (StoppedProjectedExperiment.cut (FixedRows.rows plan) hupper hij)
    (StoppedProjectedExperiment.direction (FixedRows.rows plan) hupper hij)
    (fun _ => StoppedProjectedExperiment.innerLaw (FixedRows.rows plan) hij
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper))
      (rows_positive plan) flag)
    (StoppedProjectedExperiment.outerLaw hupper hbranch) σ

theorem expectation_meetingProbability :
    (StoppedProjectedPhysicalAdvice.law clauses (FixedRows.rows plan)
      (FixedRows.repeats plan) hupper hij designated hbranch
      (rows_positive plan) flag plan.order).expectation
        (meetingProbability plan clauses hupper hij designated hbranch flag σ) =
      expectedMeeting plan clauses hupper hij designated hbranch flag σ := by
  unfold meetingProbability
  rw [StoppedProjectedPhysicalAdvice.expectation_read clauses (FixedRows.rows plan)
    (FixedRows.repeats plan) hupper hij designated hbranch
    (rows_positive plan) flag σ plan.order]
  simp only [StoppedProjectedPhysicalAdvice.rawLaw, expectedMeeting,
    HierarchicalProjectedOuterAverage.expectedMeeting,
    CandidateCoupling.expectation_sigmaLaw,
    HierarchicalProjectedAverage.expectedMeeting, rawMeetingProbability]

end
end PerfectCompleteness.StoppedProjectedMeetingLaw

end

end OAI
