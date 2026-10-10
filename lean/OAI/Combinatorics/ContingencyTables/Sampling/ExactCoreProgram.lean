import OAI.Combinatorics.ContingencyTables.Machines.OnlinePartialCall
import OAI.Combinatorics.ContingencyTables.Sampling.ExactOrdinaryProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ExactCorrectionPrefix

namespace OAI

/-! # One finite control graph for the ordinary and unbounded correction branches -/

namespace ContingencyTables.ExactCoreProgram
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeMachine (Env K encodeEnv)
open MatchingFPRAS.PhysicalStream MatchingFPRAS.OnlineStack
open ProfilePrograms DensePrograms

inductive Phase where
  | prepare | gate | choose | ordinaryInput | ordinary | rareInput | prepareRare | retry | halt
  deriving DecidableEq, Inhabited

instance : Fintype Phase := ⟨{.prepare,.gate,.choose,.ordinaryInput,.ordinary,
  .rareInput,.prepareRare,.retry,.halt},by intro x; cases x <;> simp⟩

noncomputable def instructions : Phase → OnlineControl.Instr Reg Phase
  | .prepare => .call (OnlineProc.deterministic OnlineIntegerRetry.prepareProc) .gate
  | .gate => .call rareBranchRealizer.program .choose
  | .choose => .branch 0 .ordinaryInput .rareInput
  | .ordinaryInput => .call (OnlineProc.deterministic (split 0 2 (by decide))) .ordinary
  | .ordinary => .call exactOrdinaryRealizer.program .halt
  | .rareInput => .call (OnlineProc.deterministic (split 0 2 (by decide))) .prepareRare
  | .prepareRare => .call (OnlineProc.deterministic exactMatrixInputRealizer.program) .retry
  | .retry => .call (OnlineIntegerRetry.program ExactMatrixTrial.trialRealizer) .halt
  | .halt => .halt

noncomputable def program : OnlineProc.Proc (K Reg) := OnlineControl.compile instructions

noncomputable def output (z : CompletionMargins) (s : Data) :
    Option MatrixCode → OnlinePartialCall.Config instructions
  | none => OnlinePartialCall.callCfg instructions .retry
      (OnlineControl.cfg (OnlineIntegerRetry.instructions ExactMatrixTrial.trialRealizer)
        (some .prepare) (env (TreeTyped.encode (exactMatrixInput z)) .nil s))
  | some X => OnlineControl.cfg instructions none (env (TreeTyped.encode X) .nil s)

def prefixExperiment (z : CompletionMargins) (N : ℕ) : Experiment (Option MatrixCode) :=
  (rareBranch z).bind (fun rare => if rare then correctionPrefix z N else (exactOrdinary z).map some)

/-- The failed endpoint is inside the actual retry subroutine. Its successful
endpoints have halted with the sampled matrix in the output register. -/
theorem prefix_correct (z : CompletionMargins) (s : Data) (N : ℕ) :
    ∃ p,Executes program.code program.coin (output z s)
      (OnlineTree.initial program (TreeTyped.encode z) s) p ∧
      ∀ g : Option MatrixCode → ℚ,p.mean g=(prefixExperiment z N).mean g := by
  let out := output z s
  have halted (X : MatrixCode) :
      OnlinePartialCall.At instructions out (some .halt) (env (TreeTyped.encode X) .nil s)
        (.delay 1 (.done (some X))) :=
    OnlinePartialCall.halt instructions out .halt rfl (some X) _ rfl
  have ordinary : ∃ p,OnlinePartialCall.At instructions out (some .ordinary)
      (env (TreeTyped.encode z) .nil s) p ∧
      ∀ g : Option MatrixCode → ℚ,p.mean g=((exactOrdinary z).map some).mean g := by
    obtain ⟨u,hu,hum,_⟩ := exactOrdinaryRealizer.correct z s
    refine ⟨.delay 1 (u.bind (fun X => .delay 1 (.done (some X)))),?_,?_⟩
    · exact OnlinePartialCall.call instructions out .ordinary .halt exactOrdinaryRealizer.program
        rfl _ (fun X => env (TreeTyped.encode X) .nil s) u hu _ halted
    · intro g
      simp only [Experiment.mean,Experiment.mean_bind,Experiment.mean_map]
      exact hum _
  have rare : ∃ p,OnlinePartialCall.At instructions out (some .prepareRare)
      (env (TreeTyped.encode z) .nil s) p ∧
      ∀ g : Option MatrixCode → ℚ,p.mean g=(correctionPrefix z N).mean g := by
    obtain ⟨u,hu,hum,_⟩ := OnlineIntegerRetry.prefix_correct ExactMatrixTrial.trialRealizer
      (exactMatrixInput z) s N
    let v : Option MatrixCode → Experiment (Option MatrixCode) :=
      fun o => match o with | none => .done none | some X => .delay 1 (.done (some X))
    have hcall := OnlinePartialCall.partial_call instructions .retry
      ⟨_,.halt,rfl⟩ (env (TreeTyped.encode (exactMatrixInput z)) .nil s)
      (fun o => OnlineControl.cfg (OnlineIntegerRetry.instructions ExactMatrixTrial.trialRealizer)
        (OnlineIntegerRetry.output (exactMatrixInput z) s o).1
        (OnlineIntegerRetry.output (exactMatrixInput z) s o).2) u hu
    have hv : Executes (OnlineControl.code instructions) (OnlineControl.coins instructions) out
        (OnlineControl.cfg instructions (some .retry)
          (env (TreeTyped.encode (exactMatrixInput z)) .nil s))
        ((Experiment.delay 1 u).bind v) := by
      apply hcall.bind v out
      intro o
      cases o with
      | none => exact .done none
      | some X => exact halted X
    obtain ⟨p,hp,hpm,_⟩ := OnlinePartialCall.deterministicCall instructions out .prepareRare .retry
      exactMatrixInputRealizer.program rfl _ _ _ (exactMatrixInputRealizer.correct z s)
      ((Experiment.delay 1 u).bind v) hv
    refine ⟨p,hp,?_⟩
    intro g
    rw [hpm,Experiment.mean_bind]
    simp only [Experiment.mean]
    have he : (fun o => (v o).mean g)=g := by funext o; cases o <;> rfl
    rw [he,hum]
    rfl
  have branch (b : Bool) : ∃ p,OnlinePartialCall.At instructions out (some .choose)
      (env (TreeTyped.encode b) .nil (.cons (TreeTyped.encode z) s)) p ∧
      ∀ g : Option MatrixCode → ℚ,p.mean g=
        (if b then correctionPrefix z N else (exactOrdinary z).map some).mean g := by
    cases b with
    | false =>
      obtain ⟨p,hp,hpm⟩ := ordinary
      obtain ⟨v,hv,hvm,_⟩ := OnlinePartialCall.deterministicCall instructions out
        .ordinaryInput .ordinary (split 0 2 (by decide)) rfl _ _ _
        (split02 (TreeTyped.encode false) .nil (TreeTyped.encode z) s) p hp
      refine ⟨.delay 1 v,?_,fun g => hvm g |>.trans (hpm g)⟩
      exact OnlinePartialCall.nilBranch instructions out .choose .ordinaryInput .rareInput 0 rfl _ rfl v hv
    | true =>
      obtain ⟨p,hp,hpm⟩ := rare
      obtain ⟨v,hv,hvm,_⟩ := OnlinePartialCall.deterministicCall instructions out
        .rareInput .prepareRare (split 0 2 (by decide)) rfl _ _ _
        (split02 (TreeTyped.encode true) .nil (TreeTyped.encode z) s) p hp
      refine ⟨.delay 1 v,?_,fun g => hvm g |>.trans (hpm g)⟩
      exact OnlinePartialCall.consBranch instructions out .choose .ordinaryInput .rareInput 0 rfl _
        .nil .nil rfl v hv
  choose v hv hvm using branch
  obtain ⟨u,hu,hum,_⟩ := rareBranchRealizer.correct z (.cons (TreeTyped.encode z) s)
  have hgate := OnlinePartialCall.call instructions out .gate .choose rareBranchRealizer.program
    rfl _ (fun b => env (TreeTyped.encode b) .nil (.cons (TreeTyped.encode z) s)) u hu v hv
  obtain ⟨p,hp,hpm,_⟩ := OnlinePartialCall.deterministicCall instructions out .prepare .gate
    OnlineIntegerRetry.prepareProc rfl _ _ _ (OnlineIntegerRetry.prepare_exec (TreeTyped.encode z) s)
    (.delay 1 (u.bind v)) hgate
  refine ⟨p,hp,?_⟩
  intro g
  rw [hpm]
  simp only [Experiment.mean,Experiment.mean_bind]
  simp_rw [hvm]
  rw [hum,prefixExperiment,Experiment.mean_bind]

end ContingencyTables.ExactCoreProgram

end OAI
