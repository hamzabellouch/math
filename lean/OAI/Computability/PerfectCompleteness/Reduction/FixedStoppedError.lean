import OAI.Computability.PerfectCompleteness.Foundations.StoppedSharedComparison
import OAI.Computability.PerfectCompleteness.Reduction.FixedComparisonErrorsLemmas

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedError

open FixedParameters FixedRows

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem original_calls_le {root cutoff : Nat}
    (hroot : root ≤ p.plan.depth) (hcut : cutoff ≤ root) :
    OriginalCutCalls.count (rows p.plan) (repeats p.plan) root cutoff ≤ calls p.plan := by
  have h := FixedCallBudget.pairCount_le (rows p.plan) (repeats p.plan)
    hroot (hcut.trans hroot)
  unfold FixedCallBudget.pairCount at h
  unfold calls
  omega

theorem original_calls_add_one_le {root cutoff : Nat}
    (hroot : root ≤ p.plan.depth) (hcut : cutoff ≤ root) :
    OriginalCutCalls.count (rows p.plan) (repeats p.plan) root cutoff + 1 ≤ calls p.plan := by
  have h := FixedCallBudget.pairCount_le (rows p.plan) (repeats p.plan)
    hroot (hcut.trans hroot)
  unfold FixedCallBudget.pairCount at h
  unfold calls
  omega

theorem hidden_error_lt {retained : Nat} (hcalls : retained ≤ calls p.plan) (height : Nat) :
    Real.sqrt ((ChildBlockCardinality.bound (branch p) height (sourceLength p.plan hδ)
      retained (rows p.plan) : ℝ) ^ 2 / branch p height) / 2 < p.accuracy := by
  have h := (FixedComparisonErrors.comparison_errors p hcalls height).1
  simpa only [branch, Nat.cast_pow] using h

theorem stopped_error_lt {root cut : Nat}
    (hroot : root ≤ p.plan.depth) (hcut : cut + 1 ≤ root) :
    StoppedSharedComparison.error (branch p) (rows p.plan) (repeats p.plan)
      root cut (sourceLength p.plan hδ) < p.accuracy :=
  hidden_error_lt p (original_calls_le p hroot hcut) cut

theorem collision_error_lt {root cut : Nat}
    (hroot : root ≤ p.plan.depth) (hcut : cut + 1 ≤ root) :
    Real.sqrt ((ChildBlockCardinality.bound (branch p) cut (sourceLength p.plan hδ)
      (OriginalCutCalls.count (rows p.plan) (repeats p.plan) root (cut + 1) + 1)
      (rows p.plan) : ℝ) ^ 2 / branch p cut) / 2 < p.accuracy :=
  hidden_error_lt p (original_calls_add_one_le p hroot hcut) cut

end
end PerfectCompleteness.FixedStoppedError

end

end OAI
