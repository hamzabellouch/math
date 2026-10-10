import OAI.Computability.PerfectCompleteness.Reduction.FixedStoppedError
import OAI.Computability.PerfectCompleteness.Reduction.PreliminaryOutputLemmas

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedPair

open FixedParameters FixedRows

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem exists_pair (input : List Bool) (strategy : FixedPreliminaryGame.Strategy p input)
    (hsuccess : InitialParameters.epsilon δ ≤
      (FixedPreliminaryGame.game p input).success strategy) :
    ∃ i j : Fin p.plan.depth, i < j ∧
      InitialParameters.simultaneous δ + 2 * p.accuracy ≤
        (StoppedSharedSampler.stoppedLaw
          (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
          (rows p.plan) (repeats p.plan) (cut := i.val)
          (Nat.succ_le_of_lt i.isLt) (fun k _ => branch_pos p k)
          (fun k => FixedPreliminaryGame.rows_pos p (k + 1))).probability
            (StoppedSharedEvents.pair
              (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) strategy
              (Nat.succ_le_of_lt i.isLt) (fun k _ => branch_pos p k) i j) := by
  obtain ⟨i, j, hij, hmass⟩ := PreliminaryPairReserve.exists_pair p input strategy hsuccess
  have hcut : i.val + 1 ≤ p.plan.depth := Nat.succ_le_of_lt i.isLt
  have hi : i.val + 1 ≤ i.val + 1 := le_refl _
  have hj : i.val + 1 ≤ j.val + 1 := Nat.add_le_add_right (Nat.le_of_lt hij) 1
  have htransfer := StoppedSharedComparison.pair_probability_lower
    (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) strategy
    hcut (fun k _ => branch_pos p k)
    (fun k => FixedPreliminaryGame.rows_pos p (k + 1)) i j hi hj hmass
  have herror := FixedStoppedError.stopped_error_lt p (le_refl p.plan.depth) hcut
  refine ⟨i, j, hij, ?_⟩
  linarith

end
end PerfectCompleteness.FixedStoppedPair

end

end OAI
