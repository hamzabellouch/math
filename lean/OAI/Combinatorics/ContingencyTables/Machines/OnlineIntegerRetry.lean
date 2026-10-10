import OAI.Combinatorics.ContingencyTables.Machines.OnlineRetryPrefix
import OAI.Combinatorics.MatchingCount.Machines.OnlineTree

namespace OAI

/-! # A fixed online machine for repeat-until-success -/

namespace ContingencyTables.OnlineIntegerRetry
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeMachine
open MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeTyped (Codec)
open MatchingFPRAS.RegisterProc MatchingFPRAS.OnlineStack
open MatchingFPRAS.PhysicalStream

inductive Label where
  | prepare | trial | decode | test | retry | finish | halt
  deriving DecidableEq, Inhabited

instance : Fintype Label := ⟨{.prepare,.trial,.decode,.test,.retry,.finish,.halt}, by
  intro x; cases x <;> simp⟩

def prepareProc : RegisterProc.Proc (K Reg) :=
  RegisterProc.seq (copy 0 1 (by decide)) (cons 1 2 (by decide))
def retryProc : RegisterProc.Proc (K Reg) :=
  RegisterProc.seq (split 1 2 (by decide))
    (RegisterProc.seq (copy 1 0 (by decide)) (clear 1))
def finishProc : RegisterProc.Proc (K Reg) :=
  RegisterProc.seq (clear 1)
    (RegisterProc.seq (split 1 2 (by decide)) (clear 1))

lemma prepare_exec (x s : Data) :
    RegisterProc.Exec prepareProc (encodeEnv (env x .nil s))
      (encodeEnv (env x .nil (.cons x s))) (5*TreeFunction.size x+8) := by
  exact ((copy01 x .nil s).seq (cons12 x x s)).mono (by simp only [size_nil]; omega)

lemma retry_exec (x y s : Data) :
    RegisterProc.Exec retryProc (encodeEnv (env y .nil (.cons x s)))
      (encodeEnv (env x .nil s)) (6*TreeFunction.size x+TreeFunction.size y+11) := by
  exact ((split12 y .nil x s).seq ((copy10 y x s).seq (clear1 x x s))).mono
    (by simp only [size_nil]; omega)

lemma finish_exec (x y s : Data) :
    RegisterProc.Exec finishProc (encodeEnv (env y (bit true) (.cons x s)))
      (encodeEnv (env y .nil s)) (3*TreeFunction.size x+12) := by
  exact ((clear1 y (bit true) (.cons x s)).seq
    ((split12 y .nil x s).seq (clear1 y x s))).mono (by
      simp only [bit,ite_true,size_cons,size_nil]
      omega)

variable {A B : Type} [Codec A] [Codec B] [Inhabited B]
variable {f : A → Experiment (Option B)} (F : OnlineTree.Realizer f)

def instructions : Label → OnlineControl.Instr Reg Label
  | .prepare => .call (OnlineProc.deterministic prepareProc) .trial
  | .trial => .call F.program .decode
  | .decode => .call (OnlineProc.deterministic (split 1 0 (by decide))) .test
  | .test => .branch 1 .retry .finish
  | .retry => .call (OnlineProc.deterministic retryProc) .prepare
  | .finish => .call (OnlineProc.deterministic finishProc) .halt
  | .halt => .halt

/-- A single finite control graph, independent of the number of retries. -/
def program : OnlineProc.Proc (K Reg) := OnlineControl.compile (instructions F)

def output (a : A) (s : Data) : Option B → Option Label×Env Reg
  | none => (some .prepare,env (TreeTyped.encode a) .nil s)
  | some b => (none,env (TreeTyped.encode b) .nil s)

def prefixExperiment (a : A) : ℕ → Experiment (Option B)
  | 0 => .done none
  | N+1 => (f a).bind (fun b => b.elim (prefixExperiment a N) (fun b => .done (some b)))

def stepCost (a : A) : ℕ := F.cost a+12*TreeFunction.size (TreeTyped.encode a)+TreeFunction.size (TreeTyped.encode (default : B))+40

lemma prefix_step (a : A) (s : Data) (rest : Experiment (Option B))
    (hrest : OnlineRetryPrefix.At (instructions F) (output a s)
      (some .prepare) (env (TreeTyped.encode a) .nil s) rest) :
    ∃ q,OnlineRetryPrefix.At (instructions F) (output a s)
      (some .prepare) (env (TreeTyped.encode a) .nil s) q ∧
      (∀ g : Option B → ℚ,q.mean g=
        ((f a).bind (fun b => b.elim rest (fun b => .done (some b)))).mean g) ∧
      q.cost ≤ rest.cost+stepCost F a := by
  classical
  let M:=instructions F
  let out : Option B → Option Label×Env Reg := output a s
  obtain ⟨u,hu,hum,huc⟩:=F.correct a (.cons (TreeTyped.encode a) s)
  have next (b : Option B) : ∃ q,
      OnlineRetryPrefix.At M out (some .decode)
        (env (TreeTyped.encode b) .nil (.cons (TreeTyped.encode a) s)) q ∧
      (∀ g : Option B → ℚ,q.mean g=(b.elim rest (fun b => .done (some b))).mean g) ∧
      q.cost ≤ rest.cost+6*TreeFunction.size (TreeTyped.encode a)+TreeFunction.size (TreeTyped.encode (default : B))+27 := by
    cases b with
    | none =>
      obtain ⟨v,hv,hvm,hvc⟩:=OnlineRetryPrefix.deterministicCall M out .retry .prepare
        retryProc rfl _ _ _ (retry_exec (TreeTyped.encode a) (TreeTyped.encode (default : B)) s) rest hrest
      have ht:=OnlineRetryPrefix.nilBranch M out .test .retry .finish 1 rfl
        (env (TreeTyped.encode (default : B)) (bit false) (.cons (TreeTyped.encode a) s)) rfl v hv
      obtain ⟨q,hq,hqm,hqc⟩:=OnlineRetryPrefix.deterministicCall M out .decode .test
        (split 1 0 (by decide)) rfl _ _ _
        (split10 (bit false) (TreeTyped.encode (default : B)) .nil (.cons (TreeTyped.encode a) s))
        (.delay 1 v) ht
      refine ⟨q,hq,?_,?_⟩
      · intro g
        exact (hqm g).trans (hvm g)
      · simp only [Experiment.cost,bit,Bool.false_eq_true,ite_false,size_nil] at hqc
        omega
    | some b =>
      have hh:=OnlineRetryPrefix.halt M out .halt rfl (some b) rfl
      obtain ⟨v,hv,hvm,hvc⟩:=OnlineRetryPrefix.deterministicCall M out .finish .halt
        finishProc rfl _ _ _ (finish_exec (TreeTyped.encode a) (TreeTyped.encode b) s)
        (.delay 1 (.done (some b))) hh
      have ht:=OnlineRetryPrefix.consBranch M out .test .retry .finish 1 rfl
        (env (TreeTyped.encode b) (bit true) (.cons (TreeTyped.encode a) s)) .nil .nil rfl v hv
      obtain ⟨q,hq,hqm,hqc⟩:=OnlineRetryPrefix.deterministicCall M out .decode .test
        (split 1 0 (by decide)) rfl _ _ _
        (split10 (bit true) (TreeTyped.encode b) .nil (.cons (TreeTyped.encode a) s)) (.delay 1 v) ht
      refine ⟨q,hq,?_,?_⟩
      · intro g
        exact (hqm g).trans (hvm g)
      · simp only [Experiment.cost,bit,ite_true,size_cons,size_nil] at hqc hvc
        omega
  choose v hv hvm hvc using next
  have ht:=OnlineRetryPrefix.call M out .trial .decode F.program rfl
    (env (TreeTyped.encode a) .nil (.cons (TreeTyped.encode a) s))
    (fun b => env (TreeTyped.encode b) .nil (.cons (TreeTyped.encode a) s)) u hu v hv
  obtain ⟨q,hq,hqm,hqc⟩:=OnlineRetryPrefix.deterministicCall M out .prepare .trial
    prepareProc rfl _ _ _ (prepare_exec (TreeTyped.encode a) s) (.delay 1 (u.bind v)) ht
  refine ⟨q,hq,?_,?_⟩
  · intro g
    rw [hqm,Experiment.mean,Experiment.mean_bind]
    simp_rw [hvm]
    rw [Experiment.mean_bind]
    exact hum _
  · have hb:=Experiment.cost_bind_le u v
      (rest.cost+6*TreeFunction.size (TreeTyped.encode a)+TreeFunction.size (TreeTyped.encode (default : B))+27) hvc
    simp only [Experiment.cost] at hqc
    unfold stepCost
    omega

/-- All finite prefix laws belong to the same fixed looping program.
Failure leaves the original input at the live retry entry. -/
theorem prefix_correct (a : A) (s : Data) (N : ℕ) :
    ∃ q,OnlineRetryPrefix.At (instructions F) (output a s)
      (some .prepare) (env (TreeTyped.encode a) .nil s) q ∧
      (∀ g : Option B → ℚ,q.mean g=(prefixExperiment (f := f) a N).mean g) ∧
      q.cost ≤ N*stepCost F a := by
  induction N with
  | zero => exact ⟨.done none,.done none,fun _ => rfl,by simp [Experiment.cost]⟩
  | succ N ih =>
    obtain ⟨p,hp,hpm,hpc⟩:=ih
    obtain ⟨q,hq,hqm,hqc⟩:=prefix_step F a s p hp
    refine ⟨q,hq,?_,?_⟩
    · intro g
      rw [hqm,prefixExperiment,Experiment.mean_bind,Experiment.mean_bind]
      congr 1
      funext b
      cases b <;> simp only [Option.elim_none,Option.elim_some,hpm]
    · rw [Nat.succ_mul]
      omega

/-- The finite prefixes also execute on the actual compiled tape machine.
The failed endpoint still has a live control state. -/
theorem physical_prefix (a : A) (s : Data) (N H : ℕ)
    (hH : StackCost.StackBound (OnlineTree.initial (program F) (TreeTyped.encode a) s).stk H) :
    ∃ q,PhysicalPost.Implements (OnlineStack.table (program F).code (program F).coin)
      (fun b => OnlineStack.cfg (OnlineControl.cfg (instructions F)
        (output a s b).1 (output a s b).2))
      (OnlineStack.cfg (OnlineTree.initial (program F) (TreeTyped.encode a) s)) q ∧
      (∀ g : Option B → ℚ,q.mean g=(prefixExperiment (f := f) a N).mean g) ∧
      q.cost ≤ (N*stepCost F a)*
        OnlineStack.Executes.factor (program F).code H (N*stepCost F a) := by
  obtain ⟨p,hp,hpm,hpc⟩:=prefix_correct F a s N
  have hp' : Executes (program F).code (program F).coin
      (fun b => OnlineControl.cfg (instructions F) (output a s b).1 (output a s b).2)
      (OnlineTree.initial (program F) (TreeTyped.encode a) s) p := hp
  obtain ⟨q,hq,hqm,hqc⟩:=hp'.compile H hH
  refine ⟨q,hq,fun g => (hqm g).trans (hpm g),?_⟩
  exact hqc.trans (Nat.mul_le_mul hpc
    (OnlineStack.Executes.factor_mono H H p.cost (N*stepCost F a) le_rfl hpc))

end ContingencyTables.OnlineIntegerRetry

end OAI
