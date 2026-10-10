import OAI.Combinatorics.ContingencyTables.Machines.OnlineRetryRuntime
import OAI.Combinatorics.ContingencyTables.Sampling.ExactIntegerOnline

namespace OAI

/-! # Finite expected machine time for exact binary weighted choice -/

namespace ContingencyTables.ExactIntegerPhysical
open MatchingFPRAS MatchingFPRAS.PhysicalStream ExactIntegerChoice

theorem prefix_failure_bound {r : ℕ} (w : Fin r → ℕ) (h : 0<totalWeight w) (N : ℕ) :
    (OnlineIntegerRetry.prefixExperiment (f := ExactIntegerOnline.trial) (List.ofFn w) N).mean
      (fun b => if b=none then 1 else 0) ≤ (1/2:ℚ)^N := by
  rw [ExactIntegerOnline.integer_prefix_failure w h]
  exact pow_le_pow_left₀
    (failure_nonnegative w (Nat.le_pow_clog (by decide : 1<2) (totalWeight w)))
    (failure_lt_half w (clog_power_lt_twice (totalWeight w) h)).le N

/-- The repeating finite-state bit program has summable physical halting
tail for every positive list of integer weights. -/
theorem expected_time {r : ℕ} (w : Fin r → ℕ) (h : 0<totalWeight w)
    (s : TreeData.Data) (H : ℕ)
    (hH : StackCost.StackBound
      (OnlineTree.initial (OnlineIntegerRetry.program ExactIntegerOnline.trialRealizer)
        (TreeTyped.encode (List.ofFn w)) s).stk H) :
    Summable (PhysicalRetryTail.tail
      (OnlineRetryRuntime.machineTable ExactIntegerOnline.trialRealizer)
      (OnlineRetryRuntime.initialCfg ExactIntegerOnline.trialRealizer (List.ofFn w) s)) ∧
    (∑' t,PhysicalRetryTail.tail
      (OnlineRetryRuntime.machineTable ExactIntegerOnline.trialRealizer)
      (OnlineRetryRuntime.initialCfg ExactIntegerOnline.trialRealizer (List.ofFn w) s) t) ≤
        2*(OnlineRetryRuntime.attemptBound ExactIntegerOnline.trialRealizer (List.ofFn w) H:ℝ) :=
  OnlineRetryRuntime.expected_time ExactIntegerOnline.trialRealizer (List.ofFn w) s H hH
    (prefix_failure_bound w h)

end ContingencyTables.ExactIntegerPhysical

end OAI
