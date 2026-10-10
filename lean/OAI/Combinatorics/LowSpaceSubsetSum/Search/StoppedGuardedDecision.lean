import OAI.Combinatorics.LowSpaceSubsetSum.Search.StoppedDecisionRound
import OAI.Combinatorics.LowSpaceSubsetSum.Search.GuardedDecision

namespace OAI

/-! # The fixed guard with both stopped trial algorithms

The finite decision law uses only completed watchdog executions and the
exact fallback.
-/

noncomputable section

namespace LowSpaceSubsetSum.StoppedDecision

variable {n : ℕ}

def main (I : Instance n) (hn : 180000000 ≤ n)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (hden : ((mixerSize n / 2 : ℕ) : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * (mixerSize n / 2 : ℕ))) : CorrectDecisionCore I :=
  CorrectDecisionCore.ofLaw I ((roundLaw I hn).iid (inputScale I ^ 120))
    (repeatAccept (accept I hn hscale (representationBufferCapacity n)))
    (repeated_sound I hn hscale (representationBufferCapacity n))
    (fun hsolve => (repeated_probability I hn hsolve hscale hden (representationBufferCapacity n)).le)

def guarded (T : DecisionThreshold) (I : Instance n) : CorrectDecisionCore I :=
  if h : mainGuard T.value n (inputScale I) = true then
    main I (T.large.trans (of_decide_eq_true h).1)
      (mainGuard_log (by unfold inputScale; omega : 0 < inputScale I) h)
      (T.halfGap n (of_decide_eq_true h).1)
  else fallbackDecision I

theorem guarded_sound (T : DecisionThreshold) (I : Instance n)
    (o : (guarded T I).core.Outcome) (hy : (guarded T I).core.accept o = true) : Solvable I :=
  (guarded T I).sound o hy

theorem guarded_probability (T : DecisionThreshold) (I : Instance n) (hs : Solvable I) :
    (2 / 3 : ℝ) ≤ (guarded T I).core.acceptanceProbability :=
  (guarded T I).complete hs

theorem guarded_rejects (T : DecisionThreshold) (I : Instance n) (hn : ¬ Solvable I)
    (o : (guarded T I).core.Outcome) : (guarded T I).core.accept o = false := by
  apply Bool.eq_false_iff.mpr
  intro hy
  exact hn (guarded_sound T I o hy)

end LowSpaceSubsetSum.StoppedDecision

end

end OAI
