import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalRetryTail

namespace OAI

/-! # Expected physical time of the implemented online rejection loop -/

namespace ContingencyTables.OnlineRetryRuntime
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost

variable {A B : Type} [TreeTyped.Codec A] [TreeTyped.Codec B] [Inhabited B]
variable {f : A → Experiment (Option B)} (F : OnlineTree.Realizer f)

noncomputable def machineTable :=
  OnlineStack.table (OnlineIntegerRetry.program F).code (OnlineIntegerRetry.program F).coin

noncomputable def initialCfg (a : A) (s : TreeData.Data) :=
  OnlineStack.cfg (OnlineTree.initial (OnlineIntegerRetry.program F) (TreeTyped.encode a) s)

noncomputable def outputCfg (a : A) (s : TreeData.Data) (b : Option B) :=
  OnlineStack.cfg (OnlineControl.cfg (OnlineIntegerRetry.instructions F)
    (OnlineIntegerRetry.output a s b).1 (OnlineIntegerRetry.output a s b).2)

noncomputable def attemptBound (a : A) (H : ℕ) : ℕ :=
  OnlineIntegerRetry.stepCost F a *
    OnlineStack.Executes.factor (OnlineIntegerRetry.program F).code H
      (OnlineIntegerRetry.stepCost F a) + 1

lemma output_halted (a : A) (s : TreeData.Data) (b : B) :
    (outputCfg F a s (some b)).state=none := rfl

/-- This statement concerns the fixed physical transition table of the
online loop, not only the abstract number of rejection attempts. -/
theorem expected_time (a : A) (s : TreeData.Data) (H : ℕ)
    (hH : StackCost.StackBound
      (OnlineTree.initial (OnlineIntegerRetry.program F) (TreeTyped.encode a) s).stk H)
    (hf : ∀ N,(OnlineIntegerRetry.prefixExperiment (f := f) a N).mean
      (fun b => if b=none then 1 else 0) ≤ (1/2:ℚ)^N) :
    Summable (PhysicalRetryTail.tail (machineTable F) (initialCfg F a s)) ∧
      (∑' t,PhysicalRetryTail.tail (machineTable F) (initialCfg F a s) t) ≤
        2*(attemptBound F a H:ℝ) := by
  apply GeometricRuntime.expected_time_half _ (attemptBound F a H) (Nat.zero_lt_succ _)
    (PhysicalRetryTail.tail_nonnegative _ _) (PhysicalRetryTail.tail_antitone _ _)
  intro N
  obtain ⟨q,hq,hqm,hqc⟩:=PhysicalRetryIteration.linear_physical_prefix F a s H hH N
  have hc : q.cost ≤ N*attemptBound F a H :=
    hqc.trans (Nat.mul_le_mul_left N (Nat.le_add_right _ _))
  have hb:=PhysicalRetryTail.tail_le_failure (machineTable F) (outputCfg F a s)
    (initialCfg F a s) q hq (output_halted F a s) _ hc
  have hp : (q.mean (fun b => if b=none then 1 else 0):ℝ) ≤ (1/2:ℝ)^N := by
    rw [hqm]
    have h := (Rat.cast_le (K := ℝ)).mpr (hf N)
    norm_num only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    exact h
  exact hb.trans hp

end ContingencyTables.OnlineRetryRuntime

end OAI
